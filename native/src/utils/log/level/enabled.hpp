/**
 * @file
 * \ingroup utils
 * @brief This file defines a function which returns true if the given log level is enabled
 */
#ifndef __UTILS_LOG_LEVEL_ENABLED_HPP__
#define __UTILS_LOG_LEVEL_ENABLED_HPP__

#include "access.hpp"
#include "level.hpp"


namespace Utils::Log::Level {

    /** Determine if log level l is enabled */
    [[gnu::always_inline]] static inline UTILS_LOG_LEVEL_CONSTEXPR bool enabled(const Level l) {
        return get() <= l;
    }

} // namespace Utils::Log::Level


#endif
