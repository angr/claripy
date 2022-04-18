/**
 * @file
 * \ingroup util
 */
#ifndef CONSTANT_LOG_LEVEL

    #include "access.hpp"

    #include "default.hpp"

    #include "../log.hpp"


namespace Lev = Util::Log::Level;

static std::atomic<Lev::Level> lvl { Lev::default_ };


void Lev::silent_set(const Level l) noexcept {
    lvl.store(l);
}

void Lev::set(const Level l) noexcept {
    info("Claricpp log level updating from: ", get());
    silent_set(l);
    info("Claricpp log level updated to: ", l);
}

Lev::Level Lev::get() noexcept {
    return lvl.load();
}

#endif