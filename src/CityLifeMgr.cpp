/*
 * City Life
 * Copyright (C) 2026 iCore
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

#include "CityLifeMgr.h"
#include "LifeBotReservation.h"

#include "AreaDefines.h"
#include "Chat.h"
#include "Config.h"
#include "DatabaseEnv.h"
#include "DBCStores.h"
#include "GameTime.h"
#include "Group.h"
#include "Log.h"
#include "Map.h"
#include "MapMgr.h"
#include "MotionMaster.h"
#include "MoveSplineInit.h"
#include "ObjectAccessor.h"
#include "ObjectGuid.h"
#include "Player.h"
#include "PlayerbotAI.h"
#include "Playerbots.h"
#include "PositionValue.h"
#include "Random.h"
#include "RandomPlayerbotMgr.h"
#include "SharedDefines.h"
#include "WorldSession.h"

#include <algorithm>
#include <cctype>
#include <cmath>
#include <ctime>
#include <iterator>
#include <limits>
#include <map>
#include <shared_mutex>
#include <sstream>

namespace
{
    constexpr float TwoPi = 6.28318530718f;
    constexpr uint32 ReservationSeconds = 20 * MINUTE;
    constexpr uint32 ReservationRefreshSeconds = 10 * MINUTE;
    constexpr uint32 DestinationAttempts = 6;
    constexpr uint32 MovementRetrySeconds = 15;
    constexpr uint32 MovementStallSeconds = 30;
    constexpr uint8 MovementRetryLimit = 3;
    constexpr float GroundLayerTolerance = 3.0f;
    constexpr float DestinationTolerance = 1.0f;
    constexpr float ArrivalTolerance = 1.5f;

    bool ResolveGround(Player* player, uint32 mapId, float x, float y, float& z)
    {
        MapEntry const* entry = sMapStore.LookupEntry(mapId);
        if (!player || !entry || entry->Instanceable() || !Acore::IsValidMapCoord(x, y, z))
            return false;

        Map* map = player->GetMapId() == mapId ? player->GetMap() : sMapMgr->CreateBaseMap(mapId);
        if (!map)
            return false;

        // Query the exact XY, but never snap an upstairs spot onto a distant floor below it.
        float ground = map->GetHeight(player->GetPhaseMask(), x, y, z + DestinationTolerance,
            true, GroundLayerTolerance * 2.0f);
        if (!std::isfinite(ground) || ground <= INVALID_HEIGHT ||
            std::abs(ground - z) > GroundLayerTolerance ||
            map->IsInWater(player->GetPhaseMask(), x, y, ground, player->GetCollisionHeight()))
            return false;

        // Missing MMAPs must not turn city movement into a straight-line shortcut.
        dtNavMeshQuery const* query = map->GetMapCollisionData().GetMMapData().GetNavMeshQuery();
        if (!query)
            return false;
        dtQueryFilter filter;
        filter.setIncludeFlags(NAV_GROUND);
        float const point[3] = {y, ground, x};
        float const extents[3] = {DestinationTolerance, DestinationTolerance, DestinationTolerance};
        float nearest[3] = {};
        dtPolyRef polygon = 0;
        if (dtStatusFailed(query->findNearestPoly(point, extents, &filter, &polygon, nearest)) || !polygon ||
            std::hypot(nearest[0] - y, nearest[2] - x) > DestinationTolerance ||
            std::abs(nearest[1] - ground) > DestinationTolerance)
            return false;
        z = ground;
        return true;
    }

    bool AtDestination(Player const* player, CityLife::Resident const& resident)
    {
        return player->GetMapId() == resident.TargetMap &&
            player->GetExactDist2d(resident.TargetX, resident.TargetY) <= ArrivalTolerance &&
            std::abs(player->GetPositionZ() - resident.TargetZ) <= DestinationTolerance;
    }

    std::string Lower(std::string value)
    {
        std::transform(value.begin(), value.end(), value.begin(),
            [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
        return value;
    }

    std::vector<std::string> Tokenize(std::string const& text)
    {
        std::istringstream stream(text);
        std::vector<std::string> out;
        std::string token;
        while (stream >> token)
            out.push_back(token);
        return out;
    }

    uint32 GameTimeSeconds()
    {
        return static_cast<uint32>(GameTime::GetGameTime().count());
    }

    char const* TeamName(CityLife::TeamSide team)
    {
        switch (team)
        {
            case CityLife::TeamSide::Alliance:
                return "Alliance";
            case CityLife::TeamSide::Horde:
                return "Horde";
            default:
                return "Any";
        }
    }

    char const* RaceName(uint8 race)
    {
        switch (race)
        {
            case RACE_HUMAN:
                return "Human";
            case RACE_ORC:
                return "Orc";
            case RACE_DWARF:
                return "Dwarf";
            case RACE_NIGHTELF:
                return "Night Elf";
            case RACE_UNDEAD_PLAYER:
                return "Undead";
            case RACE_TAUREN:
                return "Tauren";
            case RACE_GNOME:
                return "Gnome";
            case RACE_TROLL:
                return "Troll";
            case RACE_BLOODELF:
                return "Blood Elf";
            case RACE_DRAENEI:
                return "Draenei";
            default:
                return "Other";
        }
    }

    bool ParseTeam(std::string token, CityLife::TeamSide& out)
    {
        token = Lower(token);
        if (token == "a" || token == "ally" || token == "alliance")
        {
            out = CityLife::TeamSide::Alliance;
            return true;
        }
        if (token == "h" || token == "horde")
        {
            out = CityLife::TeamSide::Horde;
            return true;
        }
        if (token == "any" || token == "both" || token == "neutral")
        {
            out = CityLife::TeamSide::Any;
            return true;
        }
        return false;
    }

    bool ParseUInt(std::string const& text, uint32& out)
    {
        try
        {
            size_t used = 0;
            unsigned long value = std::stoul(text, &used);
            if (used != text.size() || value > std::numeric_limits<uint32>::max())
                return false;
            out = static_cast<uint32>(value);
            return true;
        }
        catch (...)
        {
            return false;
        }
    }

    bool ParseFloat(std::string const& text, float& out)
    {
        try
        {
            size_t used = 0;
            out = std::stof(text, &used);
            return used == text.size();
        }
        catch (...)
        {
            return false;
        }
    }
}

namespace CityLife
{
    Manager& Manager::Instance()
    {
        static Manager instance;
        return instance;
    }

    void Manager::LoadConfig()
    {
        bool wasEnabled = _enable;
        bool enabled = sConfigMgr->GetOption<bool>("CityLife.Enable", true);
        if (wasEnabled && !enabled && !_residents.empty())
            ReleaseAll(true);

        _enable = enabled;
        _debug = sConfigMgr->GetOption<bool>("CityLife.Debug", false);
        _startupDelaySeconds = sConfigMgr->GetOption<uint32>("CityLife.StartupDelaySeconds", 90);
        _tickSeconds = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("CityLife.TickSeconds", 10), 5, 60);

        _usePlayerbotConfig = sConfigMgr->GetOption<bool>("CityLife.Bots.UsePlayerbotConfig", true);
        _botAccountPrefix = sConfigMgr->GetOption<std::string>("CityLife.Bots.AccountPrefix", "auto");
        _botAccountMin = sConfigMgr->GetOption<uint32>("CityLife.Bots.AccountMin", 0);
        _botAccountMax = sConfigMgr->GetOption<uint32>("CityLife.Bots.AccountMax", 0);
        _botQueryLimit = std::max<uint32>(50, sConfigMgr->GetOption<uint32>("CityLife.Bots.QueryLimit", 500));
        _skipGroupedBots = sConfigMgr->GetOption<bool>("CityLife.Bots.SkipGrouped", true);
        _respectPlayerbotActivity = sConfigMgr->GetOption<bool>("CityLife.Bots.RespectPlayerbotActivity", false);
        _returnBots = sConfigMgr->GetOption<bool>("CityLife.Bots.ReturnWhenReleased", true);
        _maxTotalPopulation = std::clamp<uint32>(
            sConfigMgr->GetOption<uint32>("CityLife.Population.MaxTotal", 300), 1, 2000);
        _maxChangesPerTick = std::clamp<uint32>(
            sConfigMgr->GetOption<uint32>("CityLife.Population.MaxChangesPerTick", 3), 1, 50);

        _timeScaling = sConfigMgr->GetOption<bool>("CityLife.Time.Enable", true);
        _morningMultiplier = std::min<uint32>(200,
            sConfigMgr->GetOption<uint32>("CityLife.Time.MorningMultiplierPct", 60));
        _dayMultiplier = std::min<uint32>(200,
            sConfigMgr->GetOption<uint32>("CityLife.Time.DayMultiplierPct", 80));
        _eveningMultiplier = std::min<uint32>(200,
            sConfigMgr->GetOption<uint32>("CityLife.Time.EveningMultiplierPct", 100));
        _nightMultiplier = std::min<uint32>(200,
            sConfigMgr->GetOption<uint32>("CityLife.Time.NightMultiplierPct", 25));

        _roaming = sConfigMgr->GetOption<bool>("CityLife.Behaviour.Relocate", true);
        _relocateMinSeconds = std::max<uint32>(30,
            sConfigMgr->GetOption<uint32>("CityLife.Behaviour.RelocateMinSeconds", 180));
        _relocateMaxSeconds = std::max(_relocateMinSeconds,
            sConfigMgr->GetOption<uint32>("CityLife.Behaviour.RelocateMaxSeconds", 600));
        _leashRadius = std::max<uint32>(10,
            sConfigMgr->GetOption<uint32>("CityLife.Behaviour.LeashRadius", 35));
        _emotes = sConfigMgr->GetOption<bool>("CityLife.Behaviour.Emotes", true);
        _emoteChance = std::min<uint32>(100,
            sConfigMgr->GetOption<uint32>("CityLife.Behaviour.EmoteChancePct", 35));
        _emoteMinSeconds = std::max<uint32>(30,
            sConfigMgr->GetOption<uint32>("CityLife.Behaviour.EmoteMinSeconds", 120));
        _emoteMaxSeconds = std::max(_emoteMinSeconds,
            sConfigMgr->GetOption<uint32>("CityLife.Behaviour.EmoteMaxSeconds", 360));
        _serviceSpotWeightMultiplier = std::clamp<uint32>(
            sConfigMgr->GetOption<uint32>("CityLife.Behaviour.ServiceSpotWeightMultiplierPct", 250), 100, 1000);
        _staticServiceChance = std::min<uint32>(100,
            sConfigMgr->GetOption<uint32>("CityLife.Behaviour.StaticServiceChancePct", 80));
        _staticServiceHubs.clear();
        std::string staticHubs =
            sConfigMgr->GetOption<std::string>("CityLife.Behaviour.StaticServiceHubs", "Stormwind,Orgrimmar");
        std::replace(staticHubs.begin(), staticHubs.end(), ',', ' ');
        std::replace(staticHubs.begin(), staticHubs.end(), ';', ' ');
        for (std::string const& hub : Tokenize(staticHubs))
            _staticServiceHubs.insert(Lower(hub));
        _staticServiceCategories.clear();
        std::string staticCategories =
            sConfigMgr->GetOption<std::string>("CityLife.Behaviour.StaticServiceCategories", "auction,bank");
        std::replace(staticCategories.begin(), staticCategories.end(), ',', ' ');
        std::replace(staticCategories.begin(), staticCategories.end(), ';', ' ');
        for (std::string const& category : Tokenize(staticCategories))
            _staticServiceCategories.insert(Lower(category));
        _nonCombatStrategies = sConfigMgr->GetOption<std::string>("CityLife.Strategies.NonCombat",
            "+stay,-follow,-passive,-grind,-rpg,-travel,-duel,-pvp");

        ImportPlayerbotDefaults();
        _botAccountCache.clear();
        _startupElapsedMs = 0;
        _timerMs = 0;

        _databaseReady = VerifyDatabase();
        if (_enable && _databaseReady)
            _databaseReady = LoadData();
        if (_enable && !_databaseReady)
            _enable = false;

        LOG_INFO("module", "[CityLife] enable={} database={} hubs={} maxTotal={} timeScale={} prefix='{}'",
            _enable ? 1 : 0, _databaseReady ? 1 : 0, _hubs.size(), _maxTotalPopulation,
            _timeScaling ? 1 : 0, _botAccountPrefix);
    }

    void Manager::ImportPlayerbotDefaults()
    {
        if (!_usePlayerbotConfig)
            return;

        std::string configuredPrefix = sConfigMgr->GetOption<std::string>(
            "AiPlayerbot.RandomBotAccountPrefix", "rndbot");
        uint32 loginDelay = sConfigMgr->GetOption<uint32>("AiPlayerbot.DisabledWithoutRealPlayerLoginDelay", 30);
        std::string prefix = Lower(_botAccountPrefix);
        if (prefix.empty() || prefix == "auto" || prefix == "playerbot" || prefix == "playerbots")
            _botAccountPrefix = configuredPrefix;
        _startupDelaySeconds = std::max(_startupDelaySeconds, loginDelay);
    }

    bool Manager::VerifyDatabase()
    {
        if (!WorldDatabase.Query("SHOW TABLES LIKE 'city_life_hub'"))
        {
            LOG_ERROR("module", "[CityLife] Missing WORLD table city_life_hub. "
                "Apply data/sql/manual/world_city_life.sql");
            return false;
        }
        if (!WorldDatabase.Query("SHOW TABLES LIKE 'city_life_spot'"))
        {
            LOG_ERROR("module", "[CityLife] Missing WORLD table city_life_spot. "
                "Apply data/sql/manual/world_city_life.sql");
            return false;
        }
        return true;
    }

    bool Manager::LoadData()
    {
        std::vector<Hub> hubs;
        QueryResult hubResult = WorldDatabase.Query(
            "SELECT id,name,enabled,team,min_level,max_level,map_id,default_population,priority "
            "FROM city_life_hub ORDER BY priority DESC,id ASC");
        if (hubResult)
        {
            do
            {
                Field* fields = hubResult->Fetch();
                Hub hub;
                hub.Id = fields[0].Get<uint32>();
                hub.Name = fields[1].Get<std::string>();
                hub.Enabled = fields[2].Get<uint8>() != 0;
                hub.Team = static_cast<TeamSide>(fields[3].Get<uint8>());
                hub.MinLevel = fields[4].Get<uint8>();
                hub.MaxLevel = fields[5].Get<uint8>();
                hub.MapId = fields[6].Get<uint32>();
                hub.DefaultPopulation = fields[7].Get<uint32>();
                hub.Priority = fields[8].Get<uint32>();
                std::string configPrefix = "CityLife.Hub." + hub.Name;
                hub.ConfiguredPopulation = sConfigMgr->GetOption<uint32>(
                    configPrefix + ".Population", hub.DefaultPopulation, false);
                bool configEnabled = sConfigMgr->GetOption<bool>(
                    configPrefix + ".Enable", true, false);
                hub.Enabled = hub.Enabled && configEnabled;
                hub.UseTimeScaling = sConfigMgr->GetOption<bool>(configPrefix + ".TimeScaling", true, false);
                hub.ResidenceSeconds = sConfigMgr->GetOption<uint32>(
                    configPrefix + ".ResidenceSeconds", 0, false);
                hubs.push_back(hub);
            } while (hubResult->NextRow());
        }

        QueryResult spotResult = WorldDatabase.Query(
            "SELECT id,hub_id,name,category,x,y,z,o,radius,weight FROM city_life_spot "
            "WHERE enabled=1 ORDER BY hub_id,id");
        if (spotResult)
        {
            do
            {
                Field* fields = spotResult->Fetch();
                Spot spot;
                spot.Id = fields[0].Get<uint32>();
                spot.HubId = fields[1].Get<uint32>();
                spot.Name = fields[2].Get<std::string>();
                spot.Category = fields[3].Get<std::string>();
                spot.X = fields[4].Get<float>();
                spot.Y = fields[5].Get<float>();
                spot.Z = fields[6].Get<float>();
                spot.O = fields[7].Get<float>();
                spot.Radius = std::max(0.0f, fields[8].Get<float>());
                spot.Weight = std::max<uint32>(1, fields[9].Get<uint32>());

                auto hub = std::find_if(hubs.begin(), hubs.end(),
                    [&](Hub const& candidate) { return candidate.Id == spot.HubId; });
                if (hub != hubs.end())
                    hub->Spots.push_back(spot);
            } while (spotResult->NextRow());
        }

        _hubs.swap(hubs);
        LOG_INFO("module", "[CityLife] Loaded {} hubs and {} residents remain reserved.",
            _hubs.size(), _residents.size());
        return !_hubs.empty();
    }

    TeamSide Manager::TeamForRace(uint8 race) const
    {
        switch (race)
        {
            case RACE_HUMAN:
            case RACE_DWARF:
            case RACE_NIGHTELF:
            case RACE_GNOME:
            case RACE_DRAENEI:
                return TeamSide::Alliance;
            case RACE_ORC:
            case RACE_UNDEAD_PLAYER:
            case RACE_TAUREN:
            case RACE_TROLL:
            case RACE_BLOODELF:
                return TeamSide::Horde;
            default:
                return TeamSide::Any;
        }
    }

    Player* Manager::FindPlayer(uint32 guidLow) const
    {
        ObjectGuid guid = ObjectGuid::Create<HighGuid::Player>(guidLow);
        if (Player* player = ObjectAccessor::FindConnectedPlayer(guid))
            return player;
        return ObjectAccessor::FindPlayer(guid);
    }

    bool Manager::IsConfiguredBotAccount(uint32 accountId)
    {
        if (!accountId)
            return false;
        auto cached = _botAccountCache.find(accountId);
        if (cached != _botAccountCache.end())
            return cached->second;

        bool rangeOk = _botAccountMax > 0 && _botAccountMax >= _botAccountMin &&
            accountId >= _botAccountMin && accountId <= _botAccountMax;
        bool prefixOk = false;
        if (!_botAccountPrefix.empty())
        {
            QueryResult result = LoginDatabase.Query("SELECT username FROM account WHERE id={} LIMIT 1", accountId);
            if (result)
            {
                std::string username = Lower(result->Fetch()[0].Get<std::string>());
                prefixOk = username.rfind(Lower(_botAccountPrefix), 0) == 0;
            }
        }

        bool accepted = rangeOk || prefixOk;
        _botAccountCache[accountId] = accepted;
        return accepted;
    }

    bool Manager::IsCandidate(Player* player)
    {
        if (!player || !player->GetSession() || !player->IsInWorld() || player->IsBeingTeleported())
            return false;
        if (!sRandomPlayerbotMgr.IsRandomBot(player) &&
            !IsConfiguredBotAccount(player->GetSession()->GetAccountId()))
            return false;
        if (PlayerbotsLife::IsReserved(player->GetGUID().GetCounter()))
            return false;

        PlayerbotAI* ai = GET_PLAYERBOT_AI(player);
        if (!ai || ::IsRealPlayer(player) || ai->HasGameClientMaster())
            return false;
        if (_respectPlayerbotActivity && !ai->AllowActivity(ALL_ACTIVITY))
            return false;
        if (!player->IsAlive() || player->IsInCombat() || player->IsInFlight() || player->duel ||
            player->IsFlying() || player->GetTransport() || player->GetVehicle() || player->GetTransGUID() ||
            player->HasUnitMovementFlag(MOVEMENTFLAG_CAN_FLY | MOVEMENTFLAG_DISABLE_GRAVITY |
                MOVEMENTFLAG_ONTRANSPORT | MOVEMENTFLAG_FALLING | MOVEMENTFLAG_FALLING_FAR))
            return false;
        if (player->InBattleground() || player->InBattlegroundQueue())
            return false;
        if (player->GetMap() && player->GetMap()->Instanceable())
            return false;
        if (_skipGroupedBots && player->GetGroup())
            return false;
        return !IsResident(player->GetGUID().GetCounter());
    }

    bool Manager::IsResidentUsable(Player* player) const
    {
        if (!player || !player->GetSession() || !player->IsInWorld())
            return false;
        if (!sRandomPlayerbotMgr.IsRandomBot(player) &&
            !const_cast<Manager*>(this)->IsConfiguredBotAccount(player->GetSession()->GetAccountId()))
            return false;
        PlayerbotAI* ai = GET_PLAYERBOT_AI(player);
        if (!ai || ::IsRealPlayer(player) || ai->HasGameClientMaster())
            return false;
        if (!player->IsAlive() || player->IsInFlight() || player->duel)
            return false;
        if (player->InBattleground() || player->InBattlegroundQueue())
            return false;
        if (player->GetMap() && player->GetMap()->Instanceable())
            return false;
        if (_skipGroupedBots && player->GetGroup())
            return false;
        return true;
    }

    bool Manager::IsResident(uint32 guidLow) const
    {
        return std::any_of(_residents.begin(), _residents.end(),
            [&](Resident const& resident) { return resident.Bot.GuidLow == guidLow; });
    }

    std::vector<BotCandidate> Manager::LoadCandidates(Hub const& hub, bool applyLimit)
    {
        std::vector<BotCandidate> candidates;
        std::vector<uint32> onlineGuids;
        {
            std::shared_lock<std::shared_mutex> playerLock(*HashMapHolder<Player>::GetLock());
            HashMapHolder<Player>::MapType const& players = ObjectAccessor::GetPlayers();
            onlineGuids.reserve(players.size());
            for (auto const& pair : players)
                if (pair.second)
                    onlineGuids.push_back(pair.second->GetGUID().GetCounter());
        }

        for (uint32 guidLow : onlineGuids)
        {
            Player* player = FindPlayer(guidLow);
            if (!player || player->GetLevel() < hub.MinLevel || player->GetLevel() > hub.MaxLevel)
                continue;
            if (!IsCandidate(player))
                continue;
            if (player->GetZoneId() == AREA_WINTERGRASP)
                continue;

            BotCandidate candidate;
            candidate.GuidLow = guidLow;
            candidate.AccountId = player->GetSession()->GetAccountId();
            candidate.Name = player->GetName();
            candidate.Level = player->GetLevel();
            candidate.Race = player->getRace();
            candidate.Team = TeamForRace(candidate.Race);
            if (hub.Team != TeamSide::Any && candidate.Team != hub.Team)
                continue;
            candidates.push_back(candidate);
        }

        if (applyLimit)
        {
            for (size_t i = candidates.size(); i > 1; --i)
                std::swap(candidates[i - 1], candidates[urand(0, static_cast<uint32>(i - 1))]);
            if (candidates.size() > _botQueryLimit)
                candidates.resize(_botQueryLimit);
        }
        return candidates;
    }

    Hub* Manager::FindHub(uint32 hubId)
    {
        auto found = std::find_if(_hubs.begin(), _hubs.end(),
            [&](Hub const& hub) { return hub.Id == hubId; });
        return found == _hubs.end() ? nullptr : &*found;
    }

    Hub* Manager::FindHub(std::string const& name)
    {
        std::string lowered = Lower(name);
        auto found = std::find_if(_hubs.begin(), _hubs.end(),
            [&](Hub const& hub) { return Lower(hub.Name) == lowered; });
        return found == _hubs.end() ? nullptr : &*found;
    }

    bool Manager::IsStaticServiceSpot(Hub const& hub, Spot const& spot) const
    {
        return _staticServiceHubs.find(Lower(hub.Name)) != _staticServiceHubs.end() &&
            _staticServiceCategories.find(Lower(spot.Category)) != _staticServiceCategories.end();
    }

    Spot const* Manager::ChooseSpot(Hub const& hub, uint32 ignoredSpotId) const
    {
        Spot const* best = nullptr;
        uint64 bestScore = std::numeric_limits<uint64>::max();
        bool hasAlternative = hub.Spots.size() > 1;

        for (Spot const& spot : hub.Spots)
        {
            if (hasAlternative && spot.Id == ignoredSpotId)
                continue;
            uint32 occupants = static_cast<uint32>(std::count_if(_residents.begin(), _residents.end(),
                [&](Resident const& resident)
                {
                    return resident.HubId == hub.Id && resident.SpotId == spot.Id;
                }));
            uint64 weight = spot.Weight;
            if (IsStaticServiceSpot(hub, spot))
                weight = weight * _serviceSpotWeightMultiplier / 100;
            uint64 score = (static_cast<uint64>(occupants) + 1) * 100000 /
                std::max<uint64>(1, weight) + urand(0, 100);
            if (score < bestScore)
            {
                bestScore = score;
                best = &spot;
            }
        }
        return best;
    }

    uint32 Manager::CountResidents(uint32 hubId) const
    {
        return static_cast<uint32>(std::count_if(_residents.begin(), _residents.end(),
            [&](Resident const& resident) { return resident.HubId == hubId; }));
    }

    uint32 Manager::CurrentTimeMultiplier() const
    {
        if (!_timeScaling)
            return 100;

        std::time_t timestamp = std::time(nullptr);
        std::tm const* local = std::localtime(&timestamp);
        if (!local)
            return 100;
        std::tm localTime = *local;
        if (localTime.tm_hour >= 6 && localTime.tm_hour < 12)
            return _morningMultiplier;
        if (localTime.tm_hour >= 12 && localTime.tm_hour < 18)
            return _dayMultiplier;
        if (localTime.tm_hour >= 18)
            return _eveningMultiplier;
        return _nightMultiplier;
    }

    uint32 Manager::TargetPopulation(Hub const& hub) const
    {
        if (!hub.Enabled || hub.Spots.empty())
            return 0;
        if (!hub.UseTimeScaling)
            return hub.ConfiguredPopulation;
        return static_cast<uint32>(std::lround(
            static_cast<double>(hub.ConfiguredPopulation) * CurrentTimeMultiplier() / 100.0));
    }

    bool Manager::AssignSpot(Resident& resident, Hub const& hub, Spot const& spot, bool allowStationary)
    {
        Player* player = FindPlayer(resident.Bot.GuidLow);
        if (!player || !std::isfinite(spot.Radius) || !std::isfinite(spot.O))
            return false;

        for (uint32 attempt = 0; attempt < DestinationAttempts; ++attempt)
        {
            float const angle = frand(0.0f, TwoPi);
            float const distance = attempt + 1 < DestinationAttempts ? frand(0.0f, spot.Radius) : 0.0f;
            float const x = spot.X + std::cos(angle) * distance;
            float const y = spot.Y + std::sin(angle) * distance;
            float z = spot.Z;
            if (!ResolveGround(player, hub.MapId, x, y, z))
                continue;
            resident.HubId = hub.Id;
            resident.SpotId = spot.Id;
            resident.TargetMap = hub.MapId;
            resident.TargetX = x;
            resident.TargetY = y;
            resident.TargetZ = z;
            resident.TargetO = spot.O;
            resident.Stationary = allowStationary && IsStaticServiceSpot(hub, spot) &&
                urand(1, 100) <= _staticServiceChance;
            return true;
        }
        if (_debug)
            LOG_WARN("module", "[CityLife] No safe ground/MMAP destination for {}/{}.", hub.Name, spot.Name);
        return false;
    }

    bool Manager::AddResident(Hub const& hub)
    {
        Spot const* spot = ChooseSpot(hub);
        if (!spot)
            return false;
        std::vector<BotCandidate> candidates = LoadCandidates(hub);
        if (candidates.empty())
            return false;

        BotCandidate const& bot = candidates.front();
        Player* player = FindPlayer(bot.GuidLow);
        if (!IsCandidate(player))
            return false;
        if (!PlayerbotsLife::TryReserve(bot.GuidLow, PlayerbotsLife::ReservationOwner::CityLife))
            return false;

        Resident resident;
        resident.Bot = bot;
        resident.OriginalMap = player->GetMapId();
        resident.OriginalX = player->GetPositionX();
        resident.OriginalY = player->GetPositionY();
        resident.OriginalZ = player->GetPositionZ();
        resident.OriginalO = player->GetOrientation();
        if (!AssignSpot(resident, hub, *spot, true))
        {
            PlayerbotsLife::Release(bot.GuidLow, PlayerbotsLife::ReservationOwner::CityLife);
            return false;
        }

        uint32 now = GameTimeSeconds();
        resident.NextMoveAt = now + urand(_relocateMinSeconds, _relocateMaxSeconds);
        resident.NextEmoteAt = now + urand(_emoteMinSeconds, _emoteMaxSeconds);
        resident.NextReservationRefreshAt = now + ReservationRefreshSeconds;
        resident.ReleaseAt = hub.ResidenceSeconds == 0 ? 0 : now + hub.ResidenceSeconds;

        if (!TeleportBot(player, hub.MapId, resident.TargetX, resident.TargetY, resident.TargetZ, resident.TargetO))
        {
            PlayerbotsLife::Release(bot.GuidLow, PlayerbotsLife::ReservationOwner::CityLife);
            return false;
        }
        ApplyCityStrategies(player);
        SetStayPosition(player, resident);
        if (sRandomPlayerbotMgr.IsRandomBot(player))
            sRandomPlayerbotMgr.ScheduleTeleport(bot.GuidLow,
                std::max(ReservationSeconds, hub.ResidenceSeconds + MINUTE));
        _residents.push_back(resident);

        if (_debug)
            LOG_INFO("module", "[CityLife] Added {} (level {}) to {}/{}.",
                bot.Name, bot.Level, hub.Name, spot->Name);
        return true;
    }

    void Manager::ReleaseResident(Resident const& resident, bool returnHome)
    {
        PlayerbotsLife::Release(resident.Bot.GuidLow, PlayerbotsLife::ReservationOwner::CityLife);
        Player* player = FindPlayer(resident.Bot.GuidLow);
        if (!player || !player->GetSession())
            return;

        if (resident.MovementSplineId != 0 && player->movespline->GetId() == resident.MovementSplineId &&
            !player->IsInCombat())
            player->StopMoving();
        ClearCityStrategies(player);
        if (sRandomPlayerbotMgr.IsRandomBot(player))
            sRandomPlayerbotMgr.ScheduleTeleport(resident.Bot.GuidLow);
        if (returnHome && !player->IsBeingTeleported() && !player->IsInCombat())
        {
            if (!TeleportBot(player, resident.OriginalMap, resident.OriginalX, resident.OriginalY,
                resident.OriginalZ, resident.OriginalO) && _debug)
                LOG_WARN("module", "[CityLife] {} could not return safely; released at current position.",
                    resident.Bot.Name);
        }
    }

    void Manager::ReleaseAll(bool returnHome)
    {
        for (Resident const& resident : _residents)
            ReleaseResident(resident, returnHome && _returnBots);
        _residents.clear();
    }

    void Manager::RemoveUnavailableResidents()
    {
        uint32 now = GameTimeSeconds();
        auto resident = _residents.begin();
        while (resident != _residents.end())
        {
            Player* player = FindPlayer(resident->Bot.GuidLow);
            Hub* hub = FindHub(resident->HubId);
            bool residenceExpired = resident->ReleaseAt != 0 && resident->ReleaseAt <= now && player &&
                !player->IsInCombat() && !player->IsBeingTeleported();
            bool const movementUnavailable = player && !player->IsBeingTeleported() &&
                (player->IsFlying() || player->GetTransport() || player->GetVehicle() || player->GetTransGUID() ||
                    player->HasUnitMovementFlag(MOVEMENTFLAG_CAN_FLY | MOVEMENTFLAG_DISABLE_GRAVITY |
                        MOVEMENTFLAG_ONTRANSPORT) || (hub && player->GetMapId() != hub->MapId));
            if (!hub || !IsResidentUsable(player) || residenceExpired || movementUnavailable)
            {
                ReleaseResident(*resident, residenceExpired && _returnBots);
                resident = _residents.erase(resident);
            }
            else
                ++resident;
        }
    }

    void Manager::MaintainPopulation()
    {
        RemoveUnavailableResidents();

        std::unordered_map<uint32, uint32> targets;
        uint32 remaining = _maxTotalPopulation;
        for (Hub const& hub : _hubs)
        {
            uint32 target = std::min(TargetPopulation(hub), remaining);
            targets[hub.Id] = target;
            remaining -= target;
        }

        uint32 changes = 0;
        for (Hub const& hub : _hubs)
        {
            uint32 target = targets[hub.Id];
            while (CountResidents(hub.Id) > target && changes < _maxChangesPerTick)
            {
                auto found = std::find_if(_residents.rbegin(), _residents.rend(),
                    [&](Resident const& resident)
                    {
                        Player* player = FindPlayer(resident.Bot.GuidLow);
                        return resident.HubId == hub.Id && player && !player->IsInCombat() &&
                            !player->IsBeingTeleported();
                    });
                if (found == _residents.rend())
                    break;
                auto eraseAt = std::next(found).base();
                ReleaseResident(*eraseAt, _returnBots);
                _residents.erase(eraseAt);
                ++changes;
            }
        }

        std::unordered_set<uint32> blockedHubs;
        while (changes < _maxChangesPerTick)
        {
            Hub const* selectedHub = nullptr;
            uint32 selectedCurrent = 0;
            uint32 selectedTarget = 0;
            for (Hub const& hub : _hubs)
            {
                uint32 target = targets[hub.Id];
                uint32 current = CountResidents(hub.Id);
                if (current >= target || blockedHubs.find(hub.Id) != blockedHubs.end())
                    continue;

                bool lowerFillRatio = selectedHub &&
                    static_cast<uint64>(current) * selectedTarget <
                    static_cast<uint64>(selectedCurrent) * target;
                if (!selectedHub || lowerFillRatio)
                {
                    selectedHub = &hub;
                    selectedCurrent = current;
                    selectedTarget = target;
                }
            }

            if (!selectedHub)
                break;
            if (AddResident(*selectedHub))
            {
                ++changes;
                continue;
            }

            blockedHubs.insert(selectedHub->Id);
            if (_debug)
                LOG_INFO("module", "[CityLife] {} needs {} bots but only {} are available.",
                    selectedHub->Name, selectedTarget, selectedCurrent);
        }
    }

    void Manager::RelocateResident(Resident& resident, Hub const& hub)
    {
        Spot const* spot = ChooseSpot(hub, resident.SpotId);
        if (!spot)
            return;

        resident.NextMoveAt = GameTimeSeconds() + urand(_relocateMinSeconds, _relocateMaxSeconds);
        if (!AssignSpot(resident, hub, *spot, false))
            return;
        Player* player = FindPlayer(resident.Bot.GuidLow);
        if (!player)
            return;
        resident.MovementRetries = 0;
        resident.RetryMoveAt = GameTimeSeconds();
        if (!StartMovement(player, resident))
        {
            resident.MovementRetries = 1;
            resident.RetryMoveAt += MovementRetrySeconds;
            return;
        }

        if (_debug)
            LOG_INFO("module", "[CityLife] {} walks to {}/{}.", resident.Bot.Name, hub.Name, spot->Name);
    }

    void Manager::MaintainResidents()
    {
        uint32 now = GameTimeSeconds();
        for (Resident& resident : _residents)
        {
            Hub* hub = FindHub(resident.HubId);
            Player* player = FindPlayer(resident.Bot.GuidLow);
            if (!hub || !player || player->IsBeingTeleported())
                continue;

            if (resident.NextReservationRefreshAt <= now && sRandomPlayerbotMgr.IsRandomBot(player))
            {
                sRandomPlayerbotMgr.ScheduleTeleport(resident.Bot.GuidLow,
                    std::max(ReservationSeconds, hub->ResidenceSeconds + MINUTE));
                resident.NextReservationRefreshAt = now + ReservationRefreshSeconds;
            }

            if (player->IsInCombat() || player->duel || player->IsInFlight() ||
                player->IsNonMeleeSpellCast(false))
            {
                // Combat owns movement now. Resume with a fresh path, not an expired transit timeout.
                if (resident.Travelling)
                {
                    resident.Travelling = false;
                    resident.MovementRetries = 0;
                }
                resident.RetryMoveAt = now + MovementRetrySeconds;
                continue;
            }

            ApplyCityStrategies(player);
            if (resident.Travelling)
            {
                if (AtDestination(player, resident))
                    FinishMovement(player, resident, true);
                else
                {
                    if (player->GetExactDist(resident.ProgressX, resident.ProgressY, resident.ProgressZ) >= 1.0f)
                    {
                        resident.ProgressX = player->GetPositionX();
                        resident.ProgressY = player->GetPositionY();
                        resident.ProgressZ = player->GetPositionZ();
                        resident.LastProgressAt = now;
                    }
                    bool const ownsSpline = player->movespline->GetId() == resident.MovementSplineId;
                    if (ownsSpline && !player->movespline->Finalized() &&
                        now < resident.MovementDeadlineAt && now < resident.LastProgressAt + MovementStallSeconds)
                        continue;
                    if (ownsSpline)
                        player->StopMoving();
                    resident.Travelling = false;
                    resident.MovementSplineId = 0;
                    resident.RetryMoveAt = now + MovementRetrySeconds;
                    if (++resident.MovementRetries >= MovementRetryLimit)
                        FinishMovement(player, resident, false);
                }
                continue;
            }

            bool const drifted = player->GetMapId() != hub->MapId ||
                player->GetExactDist2d(resident.TargetX, resident.TargetY) > _leashRadius;
            bool const idleDisplaced = !player->isMoving() &&
                (player->GetExactDist2d(resident.TargetX, resident.TargetY) > 3.0f ||
                    std::abs(player->GetPositionZ() - resident.TargetZ) > DestinationTolerance);
            if ((resident.RetryMoveAt != 0 || drifted || idleDisplaced) && !AtDestination(player, resident))
            {
                if (resident.RetryMoveAt <= now && !StartMovement(player, resident))
                {
                    resident.RetryMoveAt = now + MovementRetrySeconds;
                    if (++resident.MovementRetries >= MovementRetryLimit)
                        FinishMovement(player, resident, false);
                }
                continue;
            }
            resident.RetryMoveAt = 0;

            if (_roaming && !resident.Stationary && resident.NextMoveAt <= now)
            {
                RelocateResident(resident, *hub);
                continue;
            }

            SetStayPosition(player, resident);

            if (_emotes && resident.NextEmoteAt <= now)
            {
                if (!player->isMoving() && urand(1, 100) <= _emoteChance)
                    TryEmote(player);
                resident.NextEmoteAt = now + urand(_emoteMinSeconds, _emoteMaxSeconds);
            }
        }
    }

    void Manager::ApplyCityStrategies(Player* player) const
    {
        if (PlayerbotAI* ai = GET_PLAYERBOT_AI(player))
        {
            bool needsUpdate = false;
            for (char const* strategy : {"stay", "follow", "passive", "grind", "rpg", "new rpg", "travel",
                "move random", "collision", "move from group", "quest", "loot", "gather", "duel", "pvp",
                "bg", "lfg", "start duel"})
                needsUpdate = needsUpdate || ai->HasStrategy(strategy, BOT_STATE_NON_COMBAT);
            if (needsUpdate)
            {
                ai->ChangeStrategy(_nonCombatStrategies, BOT_STATE_NON_COMBAT);
                // City Life owns non-combat transit; stay's return action otherwise launches its own path.
                // Combat strategies are untouched so residents can still defend themselves.
                ai->ChangeStrategy("-stay,-follow,-passive,-grind,-rpg,-new rpg,-travel,-move random,"
                    "-collision,-move from group,-quest,-loot,-gather,-duel,-pvp,-bg,-lfg,-start duel",
                    BOT_STATE_NON_COMBAT);
            }
        }
    }

    void Manager::SetStayPosition(Player* player, Resident const& /*resident*/) const
    {
        PlayerbotAI* ai = GET_PLAYERBOT_AI(player);
        if (!ai)
            return;
        PositionMap& positions = ai->GetAiObjectContext()->GetValue<PositionMap&>("position")->Get();
        PositionInfo stay = positions["stay"];
        stay.Set(player->GetPositionX(), player->GetPositionY(), player->GetPositionZ(), player->GetMapId());
        positions["stay"] = stay;
    }

    void Manager::ClearCityStrategies(Player* player) const
    {
        PlayerbotAI* ai = GET_PLAYERBOT_AI(player);
        if (!ai)
            return;
        PositionMap& positions = ai->GetAiObjectContext()->GetValue<PositionMap&>("position")->Get();
        PositionInfo stay = positions["stay"];
        stay.Reset();
        positions["stay"] = stay;
        ai->ResetStrategies();
    }

    bool Manager::TeleportBot(Player* player, uint32 mapId, float x, float y, float z, float o) const
    {
        if (!std::isfinite(o) || !ResolveGround(player, mapId, x, y, z) ||
            !player->TeleportTo(mapId, x, y, z, o))
            return false;
        player->GetMotionMaster()->Clear(false);
        player->GetMotionMaster()->MoveIdle();
        return true;
    }

    bool Manager::StartMovement(Player* player, Resident& resident) const
    {
        if (!player || player->GetMapId() != resident.TargetMap || player->IsBeingTeleported() ||
            player->IsInCombat() || player->IsNonMeleeSpellCast(false) ||
            player->HasUnitState(UNIT_STATE_NOT_MOVE) || player->GetTransport() || player->GetVehicle() ||
            player->GetTransGUID() || player->IsFlying() ||
            player->HasUnitMovementFlag(MOVEMENTFLAG_CAN_FLY | MOVEMENTFLAG_DISABLE_GRAVITY |
                MOVEMENTFLAG_ONTRANSPORT | MOVEMENTFLAG_FALLING | MOVEMENTFLAG_FALLING_FAR))
            return false;

        // Synchronize the spline position before validation, and remove any old movement generator.
        player->StopMoving();
        player->GetMotionMaster()->Clear(false);
        player->GetMotionMaster()->MoveIdle();
        float sourceZ = player->GetPositionZ();
        float targetZ = resident.TargetZ;
        if (!ResolveGround(player, resident.TargetMap, player->GetPositionX(), player->GetPositionY(), sourceZ) ||
            std::abs(sourceZ - player->GetPositionZ()) > DestinationTolerance ||
            !ResolveGround(player, resident.TargetMap, resident.TargetX, resident.TargetY, targetZ) ||
            std::abs(targetZ - resident.TargetZ) > DestinationTolerance)
            return false;

        PathGenerator path(player);
        path.SetSlopeCheck(true);
        if (!path.CalculatePath(resident.TargetX, resident.TargetY, targetZ, false) ||
            path.GetPathType() != PATHFIND_NORMAL || path.GetPath().size() < 2)
            return false;

        auto matchesTarget = [&](G3D::Vector3 const& point)
        {
            return std::hypot(point.x - resident.TargetX, point.y - resident.TargetY) <= DestinationTolerance &&
                std::abs(point.z - targetZ) <= DestinationTolerance;
        };
        if (!matchesTarget(path.GetActualEndPosition()) || !matchesTarget(path.GetPath().back()))
            return false;
        for (G3D::Vector3 const& point : path.GetPath())
        {
            float ground = point.z;
            if (!ResolveGround(player, resident.TargetMap, point.x, point.y, ground) ||
                std::abs(ground - point.z) > DestinationTolerance)
                return false;
        }

        ApplyCityStrategies(player);
        SetStayPosition(player, resident);
        player->SetStandState(UNIT_STAND_STATE_STAND);
        Movement::MoveSplineInit movement(player);
        movement.MovebyPath(path.GetPath());
        movement.SetWalk(true);
        movement.SetFacing(resident.TargetO);
        int32 const duration = movement.Launch();
        if (duration <= 0)
            return false;

        uint32 const now = GameTimeSeconds();
        resident.TargetZ = targetZ;
        resident.Travelling = true;
        resident.MovementSplineId = player->movespline->GetId();
        resident.MovementDeadlineAt = now + static_cast<uint32>(duration) / IN_MILLISECONDS +
            std::max(MovementStallSeconds, _tickSeconds * 2);
        resident.LastProgressAt = now;
        resident.ProgressX = player->GetPositionX();
        resident.ProgressY = player->GetPositionY();
        resident.ProgressZ = player->GetPositionZ();
        resident.RetryMoveAt = 0;
        return true;
    }

    void Manager::FinishMovement(Player* player, Resident& resident, bool arrived) const
    {
        if (resident.MovementSplineId != 0 && player->movespline->GetId() == resident.MovementSplineId)
            player->StopMoving();
        resident.Travelling = false;
        resident.MovementSplineId = 0;
        resident.MovementRetries = 0;
        resident.RetryMoveAt = 0;
        // Give up at the actual position, never teleport to an unreachable or unvalidated endpoint.
        if (!arrived)
        {
            resident.SpotId = 0;
            resident.TargetMap = player->GetMapId();
            resident.TargetX = player->GetPositionX();
            resident.TargetY = player->GetPositionY();
            resident.TargetZ = player->GetPositionZ();
            resident.TargetO = player->GetOrientation();
            if (_debug)
                LOG_WARN("module", "[CityLife] {} stopped after {} movement retries; no teleport used.",
                    resident.Bot.Name, MovementRetryLimit);
        }
        resident.NextMoveAt = GameTimeSeconds() + urand(_relocateMinSeconds, _relocateMaxSeconds);
        SetStayPosition(player, resident);
    }

    void Manager::TryEmote(Player* player) const
    {
        switch (urand(0, 5))
        {
            case 0:
                player->HandleEmoteCommand(EMOTE_ONESHOT_TALK);
                break;
            case 1:
                player->HandleEmoteCommand(EMOTE_ONESHOT_WAVE);
                break;
            case 2:
                player->HandleEmoteCommand(EMOTE_ONESHOT_BOW);
                break;
            case 3:
                player->HandleEmoteCommand(EMOTE_ONESHOT_LAUGH);
                break;
            case 4:
                player->HandleEmoteCommand(EMOTE_ONESHOT_POINT);
                break;
            default:
                player->HandleEmoteCommand(EMOTE_ONESHOT_CHEER);
                break;
        }
    }

    void Manager::Update(uint32 diff)
    {
        if (!_enable)
            return;

        if (_startupElapsedMs < _startupDelaySeconds * IN_MILLISECONDS)
        {
            _startupElapsedMs += diff;
            return;
        }

        if (_timerMs > diff)
        {
            _timerMs -= diff;
            return;
        }

        _timerMs = _tickSeconds * IN_MILLISECONDS;
        MaintainPopulation();
        MaintainResidents();
    }

    void Manager::PrintStatus(ChatHandler* handler) const
    {
        uint32 startupTarget = _startupDelaySeconds * IN_MILLISECONDS;
        uint32 startupLeft = _startupElapsedMs < startupTarget ?
            (startupTarget - _startupElapsedMs + 999) / 1000 : 0;
        handler->PSendSysMessage(
            "CityLife: enabled={} database={} startup={}s residents={}/{} time={}pct hubs={}.",
            _enable ? 1 : 0, _databaseReady ? "ready" : "missing", startupLeft,
            _residents.size(), _maxTotalPopulation, CurrentTimeMultiplier(), _hubs.size());
        for (Hub const& hub : _hubs)
        {
            handler->PSendSysMessage("{} [{}] level {}-{} base={} target={} current={} spots={} priority={}",
                hub.Name, TeamName(hub.Team), hub.MinLevel, hub.MaxLevel, hub.ConfiguredPopulation,
                TargetPopulation(hub), CountResidents(hub.Id), hub.Spots.size(), hub.Priority);
        }
    }

    void Manager::PrintRaceDistribution(ChatHandler* handler, Hub const* hub)
    {
        struct RaceCounts
        {
            uint32 Residents = 0;
            uint32 Eligible = 0;
        };

        std::map<uint8, RaceCounts> counts;
        uint32 residentTotal = 0;
        for (Resident const& resident : _residents)
        {
            if (hub && resident.HubId != hub->Id)
                continue;
            ++counts[resident.Bot.Race].Residents;
            ++residentTotal;
        }

        std::unordered_set<uint32> eligibleGuids;
        for (Hub const& candidateHub : _hubs)
        {
            if (hub ? candidateHub.Id != hub->Id : !candidateHub.Enabled || candidateHub.Spots.empty())
                continue;
            for (BotCandidate const& candidate : LoadCandidates(candidateHub, false))
                if (eligibleGuids.insert(candidate.GuidLow).second)
                    ++counts[candidate.Race].Eligible;
        }

        handler->PSendSysMessage("CityLife races: scope={} residents={} eligible={} (before QueryLimit={}).",
            hub ? hub->Name : "all", residentTotal, eligibleGuids.size(), _botQueryLimit);
        handler->PSendSysMessage(hub ?
            "Eligible = online, unreserved bots matching this hub's faction, level and safety filters." :
            "Eligible = unique online, unreserved bots matching any enabled hub with spots; no duplicate bots.");
        for (auto const& [race, count] : counts)
        {
            double residentPct = residentTotal ? 100.0 * count.Residents / residentTotal : 0.0;
            double eligiblePct = eligibleGuids.empty() ? 0.0 : 100.0 * count.Eligible / eligibleGuids.size();
            handler->PSendSysMessage("{} (race {}): residents={} ({:.1f}pct) eligible={} ({:.1f}pct).",
                RaceName(race), static_cast<uint32>(race), count.Residents, residentPct, count.Eligible, eligiblePct);
        }
        handler->PSendSysMessage("CityLife selects from eligible bots without a race preference or race balancing.");
    }

    void Manager::PrintHelp(ChatHandler* handler) const
    {
        handler->PSendSysMessage("CityLife commands:");
        handler->PSendSysMessage(".citylife status");
        handler->PSendSysMessage(".citylife races [hub|all]");
        handler->PSendSysMessage(".citylife reload");
        handler->PSendSysMessage(".citylife hub list");
        handler->PSendSysMessage(
            ".citylife hub add <name> <alliance|horde|any> <minLevel> <maxLevel> <population> [priority]");
        handler->PSendSysMessage(".citylife hub population <name> <count>");
        handler->PSendSysMessage(".citylife hub enable|disable <name>");
        handler->PSendSysMessage(".citylife spot list <hub>");
        handler->PSendSysMessage(".citylife spot add <hub> <name> <category> [weight] [radius]");
        handler->PSendSysMessage(".citylife spot delete <hub> <name>");
    }

    bool Manager::HandleHubCommand(ChatHandler* handler, std::vector<std::string> const& args)
    {
        if (args.size() < 2)
            return false;
        std::string operation = Lower(args[1]);
        if (operation == "list")
        {
            PrintStatus(handler);
            return true;
        }

        if (operation == "add")
        {
            if (args.size() < 7 || !handler->GetSession() || !handler->GetSession()->GetPlayer())
                return false;
            TeamSide team;
            uint32 minLevel;
            uint32 maxLevel;
            uint32 population;
            uint32 priority = 100;
            if (!ParseTeam(args[3], team) || !ParseUInt(args[4], minLevel) ||
                !ParseUInt(args[5], maxLevel) || !ParseUInt(args[6], population) ||
                (args.size() > 7 && !ParseUInt(args[7], priority)) || minLevel > maxLevel || maxLevel > 80)
            {
                handler->PSendSysMessage("CityLife: invalid team, level, population or priority.");
                return true;
            }

            Player* gm = handler->GetSession()->GetPlayer();
            std::string name = args[2];
            WorldDatabase.EscapeString(name);
            WorldDatabase.DirectExecute(
                "INSERT INTO city_life_hub "
                "(name,enabled,team,min_level,max_level,map_id,default_population,priority) "
                "VALUES ('{}',1,{},{},{},{},{},{}) ON DUPLICATE KEY UPDATE enabled=1,team=VALUES(team),"
                "min_level=VALUES(min_level),max_level=VALUES(max_level),map_id=VALUES(map_id),"
                "default_population=VALUES(default_population),priority=VALUES(priority)",
                name, static_cast<uint32>(team), minLevel, maxLevel, gm->GetMapId(), population, priority);
            QueryResult result = WorldDatabase.Query("SELECT id FROM city_life_hub WHERE name='{}' LIMIT 1", name);
            if (result)
            {
                uint32 hubId = result->Fetch()[0].Get<uint32>();
                WorldDatabase.DirectExecute(
                    "INSERT INTO city_life_spot (hub_id,name,category,enabled,x,y,z,o,radius,weight) "
                    "SELECT {},'MainSquare','square',1,{},{},{},{},8,100 FROM DUAL "
                    "WHERE NOT EXISTS (SELECT 1 FROM city_life_spot WHERE hub_id={})",
                    hubId, gm->GetPositionX(), gm->GetPositionY(), gm->GetPositionZ(),
                    gm->GetOrientation(), hubId);
            }
            LoadData();
            handler->PSendSysMessage("CityLife: saved hub {} at the GM position.", name);
            return true;
        }

        if ((operation == "enable" || operation == "disable") && args.size() >= 3)
        {
            std::string name = args[2];
            WorldDatabase.EscapeString(name);
            WorldDatabase.DirectExecute("UPDATE city_life_hub SET enabled={} WHERE name='{}'",
                operation == "enable" ? 1 : 0, name);
            LoadData();
            handler->PSendSysMessage("CityLife: {} {}.", name, operation == "enable" ? "enabled" : "disabled");
            return true;
        }

        if (operation == "population" && args.size() >= 4)
        {
            uint32 population;
            if (!ParseUInt(args[3], population))
                return false;
            std::string name = args[2];
            WorldDatabase.EscapeString(name);
            WorldDatabase.DirectExecute(
                "UPDATE city_life_hub SET default_population={} WHERE name='{}'", population, name);
            LoadData();
            handler->PSendSysMessage(
                "CityLife: {} database population set to {}. A config override still takes precedence.",
                name, population);
            return true;
        }
        return false;
    }

    bool Manager::HandleSpotCommand(ChatHandler* handler, std::vector<std::string> const& args)
    {
        if (args.size() < 3)
            return false;
        std::string operation = Lower(args[1]);
        Hub* hub = FindHub(args[2]);
        if (!hub)
        {
            handler->PSendSysMessage("CityLife: unknown hub '{}'.", args[2]);
            return true;
        }

        if (operation == "list")
        {
            handler->PSendSysMessage("CityLife spots for {}:", hub->Name);
            for (Spot const& spot : hub->Spots)
                handler->PSendSysMessage("#{} {} [{}] weight={} radius={} ({}, {}, {})",
                    spot.Id, spot.Name, spot.Category, spot.Weight, spot.Radius, spot.X, spot.Y, spot.Z);
            return true;
        }

        if (operation == "add")
        {
            if (args.size() < 5 || !handler->GetSession() || !handler->GetSession()->GetPlayer())
                return false;
            uint32 weight = 100;
            float radius = 4.0f;
            if ((args.size() > 5 && !ParseUInt(args[5], weight)) ||
                (args.size() > 6 && !ParseFloat(args[6], radius)))
                return false;
            weight = std::max<uint32>(1, weight);
            radius = std::clamp(radius, 0.0f, 30.0f);

            Player* gm = handler->GetSession()->GetPlayer();
            std::string spotName = args[3];
            std::string category = args[4];
            WorldDatabase.EscapeString(spotName);
            WorldDatabase.EscapeString(category);
            WorldDatabase.DirectExecute(
                "INSERT INTO city_life_spot (hub_id,name,category,enabled,x,y,z,o,radius,weight) "
                "VALUES ({},'{}','{}',1,{},{},{},{},{},{}) ON DUPLICATE KEY UPDATE category=VALUES(category),"
                "enabled=1,x=VALUES(x),y=VALUES(y),z=VALUES(z),o=VALUES(o),radius=VALUES(radius),"
                "weight=VALUES(weight)",
                hub->Id, spotName, category, gm->GetPositionX(), gm->GetPositionY(), gm->GetPositionZ(),
                gm->GetOrientation(), radius, weight);
            LoadData();
            handler->PSendSysMessage("CityLife: saved {}/{} at the GM position.", hub->Name, spotName);
            return true;
        }

        if (operation == "delete" && args.size() >= 4)
        {
            std::string spotName = args[3];
            WorldDatabase.EscapeString(spotName);
            WorldDatabase.DirectExecute("DELETE FROM city_life_spot WHERE hub_id={} AND name='{}'",
                hub->Id, spotName);
            LoadData();
            handler->PSendSysMessage("CityLife: deleted {}/{}.", hub->Name, spotName);
            return true;
        }
        return false;
    }

    bool Manager::HandleCommand(ChatHandler* handler, std::string const& text)
    {
        std::vector<std::string> args = Tokenize(text);
        if (args.empty() || Lower(args[0]) == "help")
        {
            PrintHelp(handler);
            return true;
        }

        std::string command = Lower(args[0]);
        if (command == "status")
        {
            PrintStatus(handler);
            return true;
        }
        if (command == "races")
        {
            if (args.size() > 2)
            {
                handler->PSendSysMessage("CityLife: usage: .citylife races [hub|all]");
                return true;
            }
            Hub const* hub = nullptr;
            if (args.size() == 2 && Lower(args[1]) != "all")
            {
                hub = FindHub(args[1]);
                if (!hub)
                {
                    handler->PSendSysMessage("CityLife: unknown hub '{}'. Usage: .citylife races [hub|all]", args[1]);
                    return true;
                }
            }
            PrintRaceDistribution(handler, hub);
            return true;
        }
        if (command == "reload")
        {
            if (!_databaseReady || !LoadData())
                handler->PSendSysMessage("CityLife: reload failed; check the database and server log.");
            else
                handler->PSendSysMessage("CityLife: hub and spot data reloaded.");
            return true;
        }
        if (command == "hub" && HandleHubCommand(handler, args))
            return true;
        if (command == "spot" && HandleSpotCommand(handler, args))
            return true;

        PrintHelp(handler);
        return true;
    }
}
