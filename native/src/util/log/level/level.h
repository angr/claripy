/**
 * @file
 * @brief This file defines a macro which defines log level modes
 * This exists so it can be used by the C API
 */
#ifndef R_UTIL_LOG_LEVEL_LEVEL_H_
#define R_UTIL_LOG_LEVEL_LEVEL_H_

/** A macro defining the internals of BigInt; this is needed for the C API
 *  These numbers match the python log levels, for corresponding python levels
 */
#define UTIL_LOG_LEVEL_VALS(PREFIX)                                                                \
    PREFIX##Verbose = 0, PREFIX##Debug = 10, PREFIX##Info = 20, PREFIX##Warning = 30,              \
    PREFIX##Error = 40, PREFIX##Critical = 50, PREFIX##Disabled

#endif
