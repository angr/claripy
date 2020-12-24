/**
 * @file
 @brief This file defines public logging functions
 */
#ifndef __UTILS_LOG_LOG_HPP__
#define __UTILS_LOG_LOG_HPP__

#include "private/backend.hpp"
#include "private/default.hpp"
#include "private/id.hpp"

#include "../sink.hpp"

#include <utility>


/** A macro used to define standard log functions */
#define UTILS_PRIVATE_DEFINE_LOG_LEVEL(LEVEL, NAME)                                               \
    /** Log to default log with given log level */                                                \
    template <typename... Args> void NAME(Args... args) {                                         \
        static const auto id = Private::ID<Private::Default>();                                   \
        Private::backend(id, Private::Level::LEVEL, std::forward<Args>(args)...);                 \
    }                                                                                             \
    /** Log to custom log with given log level */                                                 \
    template <typename Log, typename... Args> void NAME(Args... args) {                           \
        static const auto id = Private::ID<Log>();                                                \
        Private::backend(id, Private::Level::LEVEL, std::forward<Args>(args)...);                 \
    }


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used for logging functions
     *  Unless otherwise specified, each function in this namespace takes in const reference
     *  arguments and returns void. There are no restrictions on what types of arguments,
     *  or how many arguments are given, other than that the '<<' stream operator must be defined
     *  for the type. Optionally, a class can be provided as an extra template argument to log. If
     *  it is provided the log written to will be a custom log related to that particular class.
     *  If no custom log is specified a default log is used.
     */
    namespace Log {

        /** Log to default log */
        template <typename... Args> void debug(const Args &...args) {
#if DEBUG
            static const auto id = Private::ID<Private::Default>();
            Private::backend(id, Private::Level::Debug, args...);
#else
            sink(args...);
#endif
        }

        /** Log to custom log */
        template <typename Log, typename... Args> void debug(const Args &...args) {
#if DEBUG
            static const auto id = Private::ID<Log>();
            Private::backend(id, Private::Level::Debug, args...);
#else
            sink(args...);
#endif
        }

        /** Verbose log to default log */
        template <typename... Args> void verbose(const Args &...args) {
#if defined DEBUG && defined VERBOSE
            static const auto id = Private::ID<Private::Default>();
            Private::backend(id, Private::Level::Verbose, args...);
#else
            sink(args...);
#endif
        }

        /** Verbose log to custom log */
        template <typename Log, typename... Args> void verbose(const Args &...args) {
#if defined DEBUG && defined VERBOSE
            static const auto id = Private::ID<Log>();
            Private::backend(id, Private::Level::Verbose, args...);
#else
            sink(args...);
#endif
        }

        // Define other logs
        UTILS_PRIVATE_DEFINE_LOG_LEVEL(Warning, warning)
        UTILS_PRIVATE_DEFINE_LOG_LEVEL(Critical, critical)
        UTILS_PRIVATE_DEFINE_LOG_LEVEL(Error, error)
        UTILS_PRIVATE_DEFINE_LOG_LEVEL(Info, info)

    } // namespace Log

} // namespace Utils

#endif
