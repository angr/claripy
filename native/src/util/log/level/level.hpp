/**
 * @file
 * \ingroup util
 * @brief This file defines the Util::Log::Level typesafe enum
 * Also defines the << stream operator for this class
 */
#ifndef R_UTIL_LOG_LEVEL_LEVEL_HPP_
#define R_UTIL_LOG_LEVEL_LEVEL_HPP_


#ifdef CONSTANT_LOG_LEVEL
    /** Constexpr if and only if the log level is immutable */
    #define UTILS_LOG_LEVEL_CONSTEXPR constexpr
#else
    /** Constexpr if and only if the log level is immutable */
    #define UTILS_LOG_LEVEL_CONSTEXPR
#endif


namespace Util::Log::Level {

    /** A typesafe enum denoting different log levels
     *  The higher the level the more serious the error
     */
    enum class Level { Verbose = 0, Debug, Info, Warning, Error, Critical, Disabled };

} // namespace Util::Log::Level


#endif
