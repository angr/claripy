/**
 * @file
 * \ingroup util
 */
#include "access.hpp"

#include "default.hpp"

#include <atomic>


// For brevity
using namespace Util;
using namespace Log;
using Lvl = Level::Level;


#ifdef CONSTANT_LOG_LEVEL

static const constexpr Lvl lvl { Level::default_ };

constexpr Lvl Level::get() noexcept {
    return lvl;
}

#else

static std::atomic<Lvl> lvl(Level::default_);

void Level::set(Level l) noexcept {
    lvl.store(l);
}

Lvl Level::get() noexcept {
    return lvl.load();
}

#endif
