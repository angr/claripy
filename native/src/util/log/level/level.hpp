/**
 * @file
 * \ingroup util
 * @brief This file defines log level modes
 */
#ifndef R_UTIL_LOG_LEVEL_LEVEL_HPP_
#define R_UTIL_LOG_LEVEL_LEVEL_HPP_

#ifdef CONSTANT_LOG_LEVEL
    /** Constexpr if and only if the log level is immutable */
    #define UTIL_LOG_LEVELCONSTEXPR constexpr
#else
    /** Constexpr if and only if the log level is immutable */
    #define UTIL_LOG_LEVEL_CONSTEXPR
#endif


namespace Util::Log::Level {

    /** A mask used to define the type of comparison to be used */
    enum class Level {
        Verbose = 0,
        Debug = 10,
        Info = 20,
        Warning = 30,
        Error = 40,
        Critical = 50,
        Disabled
    };

} // namespace Util::Log::Level

#endif
