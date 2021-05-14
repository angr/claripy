/**
 * @file
 * \ingroup utils
 * @brief This file defines the << stream operator for Level::Level
 */
#ifndef R_UTILS_LOG_LEVEL_OSTREAM_HPP_
#define R_UTILS_LOG_LEVEL_OSTREAM_HPP_

#include "level.hpp"

#include <ostream>


namespace Utils::Log::Level {

    /** Define the stream operator for Utils::Log::Level */
    std::ostream &operator<<(std::ostream &os, const Utils::Log::Level::Level &l);

} // namespace Utils::Log::Level

#endif
