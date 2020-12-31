/**
 * @file
 * \ingroup utils
 * @brief This default log level
 */
#ifndef __UTILS_LOG_LEVEL_DEFAULT_HPP__
#define __UTILS_LOG_LEVEL_DEFAULT_HPP__

#include "level.hpp"

#ifndef DEFAULT_LOG_LEVEL
    #error "DEFAULT_LOG_LEVEL macro undefined"
#endif


namespace Utils::Log::Level {

    /** The default log level */
    constexpr Level default_ = Level::DEFAULT_LOG_LEVEL;

} // namespace Utils::Log::Level

#endif
