/**
 * @file
 * \ingroup util
 */
#include "claricpp.hpp"

#include "../backtrace.hpp"
#include "../log.hpp"


std::atomic_bool Util::Err::Claricpp::enable_backtraces { TRUE_IF_DEBUG };

std::atomic_bool Util::Err::Claricpp::append_backtrace { false };

/** Logs that the backtrace was toggled */
void Util::Err::Claricpp::log_atomic_change(CCSC what, const bool old, const bool new_) {
    const constexpr auto str { [](const bool b) { return b ? "enabled" : "disabled"; } };
    Util::Log::info(WHOAMI, what, " changed from ", str(old), " to ", str(new_));
}


std::ostringstream Util::Err::Claricpp::save_backtrace() noexcept {
    std::ostringstream o;
    if (backtraces_enabled()) {
        ::Util::Backtrace::backward(o, frame_offset); // Prefer 'backward' over 'native'
    }
    return o; // Copy elision or compile error :)
}
