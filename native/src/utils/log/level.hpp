/**
 * @file
 * @brief This file defines the Utils::Log::Level typesafe enum
 */
#ifndef __UTILS_LOG_LEVEL_HPP__
#define __UTILS_LOG_LEVEL_HPP__


namespace Utils::Log {

    /** A typesafe enum denoting different log levels */
    enum class Level { Debug, Verbose, Info, Warning, Error, Critical };

} // namespace Utils::Log

#endif
