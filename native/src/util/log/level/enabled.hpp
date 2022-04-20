/**
 * @file
 * \ingroup util
 * @brief This file defines a function which returns true if the given log level is enabled
 */
#ifndef R_SRC_UTIL_LOG_LEVEL_ENABLED_HPP_
#define R_SRC_UTIL_LOG_LEVEL_ENABLED_HPP_

#include "access.hpp"
#include "level.hpp"


namespace Util::Log::Level {

    /** Determine if log level l is enabled */
    [[gnu::always_inline]] static inline UTIL_LOG_LEVEL_CONSTEXPR bool
    enabled(const Lvl l) noexcept {
        return get().lvl <= l.lvl;
    }

} // namespace Util::Log::Level


#endif
