/**
 * @file
 * \ingroup util
 * @brief This file methods for accessing the Log Level
 * The methods within this file are threadsafe
 */
#ifndef R_UTIL_LOG_LEVEL_ACCESS_HPP_
#define R_UTIL_LOG_LEVEL_ACCESS_HPP_

#include "level.hpp"

#ifdef CONSTANT_LOG_LEVEL
    #include "default.hpp"
#endif


namespace Util::Log::Level {

#ifdef CONSTANT_LOG_LEVEL

    /** Return the log level */
    constexpr Level get() noexcept {
        return default_;
    }

#else

    /** Set the log level
     *  Internal logging will be limited
     */
    void silent_set(const Lvl l) noexcept;

    /** Set the log level */
    void set(const Lvl l) noexcept;

    /** Return the log level */
    Lvl get() noexcept;

#endif

} // namespace Util::Log::Level

#endif
