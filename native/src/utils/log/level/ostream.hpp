/**
 * @file
 * \ingroup utils
 * @brief This file defines the << stream operator for Level::Level
 */
#ifndef __UTILS_LOG_LEVEL_OSTREAM_HPP__
#define __UTILS_LOG_LEVEL_OSTREAM_HPP__

#include "level.hpp"

#include <ostream>


namespace Utils::Log::Level {

    /** Define the stream operator for Utils::Log::Level */
    std::ostream &operator<<(std::ostream &os, const Utils::Log::Level::Level &l);

} // namespace Utils::Log::Level

#endif
