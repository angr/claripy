/**
 * @file
 * @brief This file defines log level modes
 */
#ifndef R_UTIL_LOG_LEVEL_LEVEL_HPP_
#define R_UTIL_LOG_LEVEL_LEVEL_HPP_

extern "C" {
#include "level.h"
};

namespace Util::Log::Level {

    /** A mask used to define the type of comparison to be used */
    enum class Level { UTIL_LOG_LEVEL_VALS() };

} // namespace Util::Log::Level

#endif
