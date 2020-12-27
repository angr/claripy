/**
 * @file
 * @brief This file methods for accessing the Log Level
 * The methods within this file are threadsafe
 */
#ifndef __UTILS_LOG_LEVEL_ACCESS_HPP__
#define __UTILS_LOG_LEVEL_ACCESS_HPP__

#include "level.hpp"


namespace Utils::Log::Level {

#ifdef RUNTIME_LOGLEVEL
    /** Set the log level */
    void set(Level l);
#endif

    /** Return the log level */
    Level get();

} // namespace Utils::Log::Level

#endif
