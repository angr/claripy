/**
 * @file
 * @brief This file defines the default log style
 */
#ifndef __UTILS_LOG_STYLE_DEFAULT_HPP__
#define __UTILS_LOG_STYLE_DEFAULT_HPP__

#include "level_timestamp_message.hpp"


namespace Utils::Log::Style {

    /** Define the default log style */
    using Default = LevelTimestampMessage;

} // namespace Utils::Log::Style

#endif
