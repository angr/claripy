/**
 * @file
 * @brief This file defines the log level enabled booleans
 * These are initalized by the cpp file
 */
#ifndef __UTILS_LOG_PRIVATE_RUNTIMELEVELCONFIG_HPP__
#define __UTILS_LOG_PRIVATE_RUNTIMELEVELCONFIG_HPP__

#if 0
    /** constexpr if and only if RUNTIME_LOGLEVEL is off */
    #define RUNTIME_LOG_CONSTEXPR
    /** constexpr const bool if and only if RUNTIME_LOGLEVEL is off */
    #define RUNTIME_LOG_VARIABLE_TYPE extern bool
    /** constexpr if and only if RUNTIME_LOGLEVEL is off */
    #define RUNTIME_LOG_CONSTEXPR constexpr
    /** constexpr const if and only if RUNTIME_LOGLEVEL is off */
    #define RUNTIME_LOG_VARIABLE_TYPE constexpr const bool
#endif

namespace Utils::Log::Private::Enabled {

    /** Enable / disable verbose log level */
    extern bool verbose;
    /** Enable / disable debug log level */
    extern bool debug;
    /** Enable / disable info log level */
    extern bool info;
    /** Enable / disable warning log level */
    extern bool warning;
    /** Enable / disable error log level */
    extern bool error;
    /** Enable / disable critical log level */
    extern bool critical;

} // namespace Utils::Log::Private::Enabled

#endif
