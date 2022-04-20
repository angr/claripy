/**
 * @file
 * \ingroup util
 * @brief This default log level
 */
#ifndef R_SRC_UTIL_LOG_LEVEL_DEFAULT_HPP_
#define R_SRC_UTIL_LOG_LEVEL_DEFAULT_HPP_

#include "level.hpp"

#ifndef DEFAULT_LOG_LEVEL
    #error "DEFAULT_LOG_LEVEL macro undefined"
#endif


namespace Util::Log::Level {

    /** The default log level */
    constexpr Lvl default_ { Level::DEFAULT_LOG_LEVEL };

} // namespace Util::Log::Level

#endif
