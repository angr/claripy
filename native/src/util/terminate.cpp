/**
 * @file
 * \ingroup util
 */
#include "terminate.hpp"

#include "fallback_error_log.hpp"
#include "log.hpp"


[[noreturn]] void Util::terminate(CCSC msg, const bool force_flush_log) noexcept {
    UTIL_NEW_FALLBACK_ERROR_LOG(msg);
    if (force_flush_log) {
        Util::Log::Backend::get()->flush();
    }
    std::terminate();
}
