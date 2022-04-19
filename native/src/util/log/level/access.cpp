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


void Level::silent_set(const Lvl l) noexcept {
    lvl.store(l);
}

void Level::set(const Lvl l) noexcept {
    ::Util::Log::info("Claricpp log level updating from: ", get());
    silent_set(l);
    ::Util::Log::info("Claricpp log level updated to: ", l);
}

Level::Lvl Level::get() noexcept {
    return lvl.load();
}

#endif