/**
 * @file
 * \ingroup util
 */
#include "terminate.hpp"

#include "fallback_error_log.hpp"
#include "log.hpp"


[[noreturn]] void Util::terminate(CCSC msg, const bool force_flush_log) noexcept {
    if (force_flush_log) {
        Util::Log::Backend::get()->flush();
    }
    Util::fallback_error_log(msg);
    std::terminate();
}
