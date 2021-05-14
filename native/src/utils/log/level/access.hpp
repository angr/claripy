/**
 * @file
 * \ingroup utils
 * @brief This file methods for accessing the Log Level
 * The methods within this file are threadsafe
 */
#ifndef R_UTILS_LOG_LEVEL_ACCESS_HPP_
#define R_UTILS_LOG_LEVEL_ACCESS_HPP_

#include "level.hpp"


namespace Utils::Log::Level {

#ifdef CONSTANT_LOG_LEVEL

    /** Return the log level */
    constexpr Level get() noexcept;

#else

    /** Set the log level */
    void set(Level l) noexcept;

    /** Return the log level */
    Level get() noexcept;

#endif

} // namespace Utils::Log::Level

#endif
