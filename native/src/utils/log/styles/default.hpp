/**
 * @file
 * @brief This file defines the default Log Style
 */
#ifndef __UTILS_LOG_STYLE_DEFAULT_HPP__
#define __UTILS_LOG_STYLE_DEFAULT_HPP__

#include "level_timestamp_message.hpp"


namespace Utils::Log::Style {

    /** Define the default log style
     *  This must be default constructable
     */
    using Default = LevelTimestampMessage;

} // namespace Utils::Log::Style

#endif
