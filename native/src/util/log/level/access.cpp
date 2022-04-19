/**
 * @file
 * \ingroup util
 */
#ifndef CONSTANT_LOG_LEVEL

    #include "access.hpp"

    #include "default.hpp"

    #include "../log.hpp"


namespace Level = Util::Log::Level;

static std::atomic<Level::Lvl> lvl { Level::default_ };


Level::Lvl Level::silent_set(const Lvl l) noexcept {
    return lvl.exchange(l);
}

Level::Lvl Level::set(const Lvl l) noexcept {
    const Lvl old { silent_set(l) };
    if (l != old) {
        ::Util::Log::info("Claricpp log level updated: ", old, " --> ", l);
    }
    return old;
}

Level::Lvl Level::get() noexcept {
    return lvl.load();
}

#endif