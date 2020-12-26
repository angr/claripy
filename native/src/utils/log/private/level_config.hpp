/**
 * @file
 * @brief This file defines which level_config to use
 */
#ifndef __UTILS_LOG_PRIVATE_LEVELCONFIG_HPP__
#define __UTILS_LOG_PRIVATE_LEVELCONFIG_HPP__

/** Include the appropriate header */
#ifdef RUNTIME_LOGLEVEL
    #include "runtime_level_config.hpp"
    /** constexpr if and only if RUNTIME_LOGLEVEL is undefined
     *  This is useful for things that may want to use a constexpr only if log level is runtime
     *  configurable
     */
    #define RUNTIME_LOG_CONSTEXPR
#else
    #include "compiletime_level_config.hpp"
    #define RUNTIME_LOG_CONSTEXPR constexpr
#endif


#endif
