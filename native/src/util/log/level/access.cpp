/**
 * @file
 * \ingroup util
 */
#ifndef CONSTANT_LOG_LEVEL

    #include "access.hpp"

    #include "default.hpp"

    #include "../log.hpp"


namespace Level = Util::Log::Level;

static std::atomic<Level::Level> lvl { Level::default_ };

void Level::set(Level l) noexcept {
    info(WHOAMI "Log level updating from: ", get());
    lvl.store(l);
    info(WHOAMI "Log level updated to: ", l);
}

Level::Level Level::get() noexcept {
    return lvl.load();
}

#endif