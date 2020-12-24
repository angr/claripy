/**
 * @file
 * @brief This file defines the Utils::Log::Level typesafe enum
 */
#ifndef __UTILS_LOG_LEVEL_HPP__
#define __UTILS_LOG_LEVEL_HPP__

#include <map>


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used for logging functions
     *  Unless otherwise specified, each public logging function in this namespace takes in
     * whatever arguments it is given by copy, and returns void. There are no restrictions on what
     * types of arguments, or how many arguments are given, other than that the '<<' stream
     * operator must be defined for the type. Optionally, a class can be provided as an extra
     * template argument to log. If it is provided the log written to will be a custom log related
     * to that particular class. If no custom log is specified a default log is used.
     */
    namespace Log {

        /** A typesafe enum denoting different log levels */
        enum class Level { Debug, Verbose, Info, Warning, Error, Critical };

    } // namespace Log

} // namespace Utils

#endif
