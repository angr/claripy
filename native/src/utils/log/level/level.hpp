/**
 * @file
 * \ingroup utils
 * @brief This file defines the Utils::Log::Level typesafe enum
 * Also defines the << stream operator for this class
 */
#ifndef __UTILS_LOG_LEVEL_LEVEL_HPP__
#define __UTILS_LOG_LEVEL_LEVEL_HPP__


#ifdef CONSTANT_LOG_LEVEL
    /** Constexpr if and only if the log level is immutable */
    #define UTILS_LOG_LEVEL_CONSTEXPR constexpr
#else
    /** Constexpr if and only if the log level is immutable */
    #define UTILS_LOG_LEVEL_CONSTEXPR
#endif


namespace Utils::Log::Level {

    /** A typesafe enum denoting different log levels
     *  The higher the level the more serious the error
     */
    enum class Level { Verbose = 0, Debug, Info, Warning, Error, Critical, Disabled };

} // namespace Utils::Log::Level


#endif
