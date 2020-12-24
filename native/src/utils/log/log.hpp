/**
 * @file
 * @brief This file defines public logging functions
 */
#ifndef __UTILS_LOG_LOG_HPP__
#define __UTILS_LOG_LOG_HPP__

#include "level.hpp"
#include "macros.hpp"
#include "private/level_config.hpp"
#include "private/log.hpp"

#include "../sink.hpp"

#include <utility>


/** A macro used to define standard log functions */
#define UTILS_PRIVATE_DEFINE_LOG_LEVEL(LEVEL, NAME)                                               \
    /** Log to default log with given log level */                                                \
    template <typename... Args> void NAME(Args... args) {                                         \
        if constexpr (Private::Enabled::NAME) {                                                   \
            static constexpr auto id = Default::log_id;                                           \
            Private::backend(id, Level::LEVEL, std::forward<Args>(args)...);                      \
        }                                                                                         \
        else {                                                                                    \
            sink(args...);                                                                        \
        }                                                                                         \
    }                                                                                             \
    /** Log to custom log with given log level */                                                 \
    template <typename Log, typename... Args> void NAME(Args... args) {                           \
        if constexpr (Private::Enabled::NAME) {                                                   \
            static constexpr auto id = Log::log_id;                                               \
            Private::backend(id, Level::LEVEL, std::forward<Args>(args)...);                      \
        }                                                                                         \
        else {                                                                                    \
            sink(args...);                                                                        \
        }                                                                                         \
    }


/** A namespace used for the utils directory */
namespace Utils {

    /** Define the default log class */
    UTILS_LOG_DEFINE_LOG_CLASS(Default)

    /** A namespace used for logging functions
     *  Unless otherwise specified, each function in this namespace takes in const reference
     *  arguments and returns void. There are no restrictions on what types of arguments,
     *  or how many arguments are given, other than that the '<<' stream operator must be defined
     *  for the type. Optionally, a class can be provided as an extra template argument to log. If
     *  it is provided the log written to will be a custom log related to that particular class.
     *  The Log class must have a static constexpr const char * const log_id definded.
     *  If no custom log is specified a default log is used.
     */
    namespace Log {

        // Define all log functions
        UTILS_PRIVATE_DEFINE_LOG_LEVEL(Verbose, verbose)
        UTILS_PRIVATE_DEFINE_LOG_LEVEL(Debug, debug)
        UTILS_PRIVATE_DEFINE_LOG_LEVEL(Info, info)
        UTILS_PRIVATE_DEFINE_LOG_LEVEL(Warning, warning)
        UTILS_PRIVATE_DEFINE_LOG_LEVEL(Error, error)
        UTILS_PRIVATE_DEFINE_LOG_LEVEL(Critical, critical)

    } // namespace Log

} // namespace Utils

#endif
