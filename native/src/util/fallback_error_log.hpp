/**
 * @file
 * \ingroup util
 * @brief This file defines an alternative to Util::Log::error and Util::Log::critical
 * This will log to standard error and should be used extremely sparingly and only Log cannot
 */
#ifndef R_UTIL_FALLBACKERRORLOG_HPP_
#define R_UTIL_FALLBACKERRORLOG_HPP_

#include <iostream>

namespace Util {

    /** Logs what to stderr, will catch any exception */
    inline void fallback_error_log(CCSC what) noexcept {
        if (what != nullptr) {
            try {
                // In case flushing causes an error we call it separately
                std::cerr << what << '\n'; // No flush
                std::cerr.flush();         // Distinct flush call
            }
            catch (...) {
            }
        }
    }

} // namespace Util

#endif
