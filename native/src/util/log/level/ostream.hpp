/**
 * @file
 * \ingroup util
 * @brief This file defines the << stream operator for Level::Level
 */
#ifndef R_UTIL_LOG_LEVEL_OSTREAM_HPP_
#define R_UTIL_LOG_LEVEL_OSTREAM_HPP_

#include "level.hpp"

#include <ostream>


namespace Util::Log::Level {

    /** Define the stream operator for Util::Log::Level */
    std::ostream &operator<<(std::ostream &os, const Util::Log::Level::Level &l);

} // namespace Util::Log::Level

#endif
