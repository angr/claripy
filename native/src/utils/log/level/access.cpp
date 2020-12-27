/** @file */
#include "access.hpp"

#include "default.hpp"

#include <atomic>


// For brevity
using namespace Utils;
using namespace Log;
using Lvl = Level::Level;


#if RUNTIME_LOGLEVEL

static std::atomic<Lvl> lvl(Level::default_);

void Level::set(Level l) {
    lvl.store(l);
}
Lvl Level::get() {
    return lvl.load();
}

#else

static constexpr Lvl lvl = Level::default_;

Lvl Level::get() {
    return lvl;
}

#endif
