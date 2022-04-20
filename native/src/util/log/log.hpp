/**
 * @file
 * \ingroup util
 * @brief This file defines public logging functions
 */
#ifndef R_SRC_UTIL_LOG_LOG_HPP_
#define R_SRC_UTIL_LOG_LOG_HPP_

#include "level.hpp"
#include "macros.hpp"
#include "private/send_to_backend.hpp"

#include "../lazy_str.hpp"
#include "../sink.hpp"

#include <tuple>


/** A local macro used to define standard log functions */
#define DEFINE_LOG_LEVEL(LEVEL)                                                                    \
    /** Log to a given log with given log level */                                                 \
    template <typename Log, typename... Args> inline void LEVEL(Args &&...args) {                  \
        if UTIL_LOG_LEVEL_CONSTEXPR (Level::enabled(Level::LEVEL)) {                               \
            static UTIL_LOG_LEVEL_CONSTEXPR const LogID id { Log::log_id };                        \
            Private::send_to_backend(                                                              \
                id, Level::LEVEL,                                                                  \
                Util::ConcreteLazyStr(std::make_tuple(std::forward<Args>(args)...)));              \
        }                                                                                          \
        else {                                                                                     \
            sink(std::forward<Args>(args)...); /* nop */                                           \
        }                                                                                          \
    }                                                                                              \
    /** Log to default log with given log level */                                                 \
    template <typename... Args> [[gnu::always_inline]] inline void LEVEL(Args &&...args) {         \
        LEVEL<Claricpp>(std::forward<Args>(args)...);                                              \
    }


namespace Util::Log {

    /** Define the default log class */
    UTIL_LOG_DEFINE_LOG_CLASS(Claricpp)

    // Define all log functions
    DEFINE_LOG_LEVEL(verbose)
    DEFINE_LOG_LEVEL(debug)
    DEFINE_LOG_LEVEL(info)
    DEFINE_LOG_LEVEL(warning)
    DEFINE_LOG_LEVEL(error)
    DEFINE_LOG_LEVEL(critical)

} // namespace Util::Log

// Cleanup local macros
#undef DEFINE_LOG_LEVEL

#endif
