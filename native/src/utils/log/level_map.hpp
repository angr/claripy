/**
 * @file
 * @brief This file defines a map from the Utils::Log::Level's to their string representations
 */
#ifndef __UTILS_LOG_LEVELMAP_HPP__
#define __UTILS_LOG_LEVELMAP_HPP__

#include "level.hpp"

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

        /** A map that maps a Level enum to its name */
        const extern std::map<Level, const char *const> level_map;

    } // namespace Log

} // namespace Utils

#endif
