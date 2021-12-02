/**
 * @file
 * \ingroup util
 */
#ifndef CONSTANT_LOG_LEVEL

    #include "access.hpp"

    #include "default.hpp"

    #include <atomic>

namespace Level = Util::Log::Level;

static std::atomic<Level::Level> lvl { Level::default_ };

void Level::set(Level l) noexcept {
    lvl.store(l);
}

Level::Level Level::get() noexcept {
    return lvl.load();
}

#endif