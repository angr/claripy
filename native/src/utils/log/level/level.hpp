/**
 * @file
 * @brief This file defines the Utils::Log::Level typesafe enum
 * Also defines the << stream operator for this class
 */
#ifndef __UTILS_LOG_LEVEL_LEVEL_HPP__
#define __UTILS_LOG_LEVEL_LEVEL_HPP__

#include <ostream>


namespace Utils::Log::Level {

    /** A typesafe enum denoting different log levels
     *  The higher the level the more serious the error
     */
    enum class Level { Verbose = 0, Debug, Info, Warning, Error, Critical, Disabled };

} // namespace Utils::Log::Level

/** Define the stream operator for Utils::Log::Level */
std::ostream &operator<<(std::ostream &os, const Utils::Log::Level::Level &l);

#endif
