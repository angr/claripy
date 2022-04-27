/**
 * @file
 * \ingroup util
 */
#include "claricpp.hpp"

#include "../backtrace.hpp"
#include "../fallback_error_log.hpp"
#include "../log.hpp"

// For brevity
using C = Util::Err::Claricpp;

// Statics
thread_local std::deque<C::LazyTrace::Ptr> C::backtraces {};
std::atomic_bool C::enable_backtraces { TRUE_IF_DEBUG };

// Functions
void Util::Err::Claricpp::log_atomic_change(CCSC what, const bool old, const bool new_) noexcept {
    const constexpr auto str { [](const bool b) { return b ? "enabled" : "disabled"; } };
    try {
        Util::Log::info("Util::Err::Claricpp: ", what, " changed from ", str(old), " to ",
                        str(new_));
    }
    catch (std::exception &e) {
        UTIL_NEW_FALLBACK_ERROR_LOG(
            "Util::Err::Claricpp: ", what, " changed from ", (old ? "true" : "false"), " to ",
            (new_ ? "true" : "false"),
            "\nLog failure! Fallback log was used. Log exception: ", e.what());
    }
}

void Util::Err::Claricpp::warn_backtrace_slow() noexcept {
    static constexpr CCSC msg {
        "Backtraces enabled; Claricpp exceptions will generate a backtrace on creation! This will "
        "slow down the program whenever exceptions are created!"
    };
    try {
        Util::Log::warning(msg);
    }
    UTIL_FALLBACKLOG_CATCH(msg, "\nLog failure! Fallback log was used. Logging failed");
}

void Util::Err::Claricpp::save_backtrace() noexcept try {
    backtraces.emplace_front(LazyTrace::create(frame_offset));
    if (backtraces.size() > n_backtraces) {
        backtraces.pop_back();
    }
}
UTIL_FALLBACKLOG_CATCH("Failed to save backtrace");
