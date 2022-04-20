/**
 * @file
 * \ingroup util
 * @brief This file defines the default Log Style
 */
#ifndef R_SRC_UTIL_LOG_STYLE_DEFAULT_HPP_
#define R_SRC_UTIL_LOG_STYLE_DEFAULT_HPP_

#include "level_timestamp_message.hpp"


namespace Util::Log::Style {

    /** Define the default log style
     *  This must be default constructable
     */
    using Default = LevelTimestampMessage;

} // namespace Util::Log::Style

#endif
