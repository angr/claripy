/**
 * @file
 * @brief This file methods for accessing the Log Level
 * The methods within this file are threadsafe
 */
#ifndef __UTILS_LOG_LEVEL_ACCESS_HPP__
#define __UTILS_LOG_LEVEL_ACCESS_HPP__

#include "level.hpp"


namespace Utils::Log::Level {

#ifdef CONSTANT_LOG_LEVEL

    /** Return the log level */
    constexpr Level get();

#else

    /** Set the log level */
    void set(Level l);

    /** Return the log level */
    Level get();

#endif

} // namespace Utils::Log::Level

#endif
