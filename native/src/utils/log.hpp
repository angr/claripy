/**
 * @file
 @brief This file defines logging functions
 */
#ifndef __UTILS_LOG_HPP__
#define __UTILS_LOG_HPP__

#include "private/log.hpp"
#include "sink.hpp"

#include <utility>


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used for logging functions
     *  Unless otherwise specified, each function in this namespace takes in whatever arguments it
     * is given by copy, and returns void. There are no restrictions on what types of arguments, or
     * how many arguments are given, other than that the '<<' stream operator must be defined for
     * the type
     */
    namespace Log {

        /** Normal logging */
        template <typename... Args> void log(Args... args) {
#if DEBUG
            Private::log(std::forward<Args>(args)..., Private::LogLevel::Status);
#else
            sink(args...);
#endif
        }

        /** A function used to log anything with the << stream operator defined */
        template <typename... Args> void verbose(Args... args) {
#if defined DEBUG && defined VERBOSE
            Private::log(std::forward<Args>(args)..., Private::LogLevel::Verbose);
#else
            sink(args...);
#endif
        }

    } // namespace Log

} // namespace Utils

#endif
