/**
 * @file
 * \ingroup utils
 * @brief This file defines public logging functions
 */
#ifndef __UTILS_LOG_LOG_HPP__
#define __UTILS_LOG_LOG_HPP__

#include "level.hpp"
#include "macros.hpp"
#include "private/send_to_backend.hpp"

#include "../sink.hpp"


/** A local macro used to define standard log functions */
#define DEFINE_LOG_LEVEL(LEVEL, NAME)                                                             \
    /** Log to a given log with given log level */                                                \
    template <typename Log, typename... Args> void NAME(const Args &...args) {                    \
        if UTILS_LOG_LEVEL_CONSTEXPR (Level::enabled(Level::Level::LEVEL)) {                      \
            static UTILS_LOG_LEVEL_CONSTEXPR const LogID id { Log::log_id };                      \
            Private::send_to_backend(id, Level::Level::LEVEL, args...);                           \
        }                                                                                         \
        else {                                                                                    \
            sink(args...);                                                                        \
        }                                                                                         \
    }                                                                                             \
    /** Log to default log with given log level */                                                \
    template <typename... Args> inline void NAME(const Args &...args) { NAME<Default>(args...); }


namespace Utils::Log {

    /** Define the default log class */
    UTILS_LOG_DEFINE_LOG_CLASS(Default)

    // Define all log functions
    DEFINE_LOG_LEVEL(Verbose, verbose)
    DEFINE_LOG_LEVEL(Debug, debug)
    DEFINE_LOG_LEVEL(Info, info)
    DEFINE_LOG_LEVEL(Warning, warning)
    DEFINE_LOG_LEVEL(Error, error)
    DEFINE_LOG_LEVEL(Critical, critical)

} // namespace Utils::Log

// Cleanup local macros
#undef DEFINE_LOG_LEVEL

#endif
