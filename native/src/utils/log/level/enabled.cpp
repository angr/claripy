/** @file */
#include "enabled.hpp"

#include "access.hpp"


// For brevity
using namespace Utils::Log;

/** Determine if log level l is enabled */
bool Level::enabled(const Level l) {
    return get() <= l;
}
