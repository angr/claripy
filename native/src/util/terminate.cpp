/**
 * @file
 * \ingroup util
 */
#include "terminate.hpp"

#include "log.hpp"

#include <exception>

[[noreturn]] void Util::terminate(const bool force_flush_log) noexcept {
    if (force_flush_log) {
        Util::Log::Backend::get()->flush();
    }
    std::terminate();
}
