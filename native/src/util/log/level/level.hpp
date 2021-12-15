/**
 * @file
 * @brief This file defines log level modes
 */
#ifndef R_UTIL_LOG_LEVEL_LEVEL_HPP_
#define R_UTIL_LOG_LEVEL_LEVEL_HPP_

extern "C" {
#include "level.h"
};


#ifdef CONSTANT_LOG_LEVEL
    /** Constexpr if and only if the log level is immutable */
    #define UTIL_LOG_LEVELCONSTEXPR constexpr
#else
    /** Constexpr if and only if the log level is immutable */
    #define UTIL_LOG_LEVEL_CONSTEXPR
#endif


namespace Util::Log::Level {

    /** A mask used to define the type of comparison to be used */
    enum class Level { UTIL_LOG_LEVEL_VALS() };

} // namespace Util::Log::Level

#endif
