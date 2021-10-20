/**
 * @file
 * \ingroup util
 * @brief This file methods for accessing the Log Level
 * The methods within this file are threadsafe
 */
#ifndef R_UTIL_LOG_LEVEL_ACCESS_HPP_
#define R_UTIL_LOG_LEVEL_ACCESS_HPP_

#include "level.hpp"


namespace Util::Log::Level {

#ifdef CONSTANT_LOG_LEVEL

    /** Return the log level */
    constexpr Level get() noexcept;

#else

    /** Set the log level */
    void set(Level l) noexcept;

    /** Return the log level */
    Level get() noexcept;

#endif

} // namespace Util::Log::Level

#endif
