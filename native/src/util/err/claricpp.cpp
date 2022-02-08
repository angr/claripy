/**
 * @file
 * \ingroup util
 */
#include "claricpp.hpp"

#include "../backtrace.hpp"
#include "../fallback_error_log.hpp"
#include "../log.hpp"


std::atomic_bool Util::Err::Claricpp::enable_backtraces { TRUE_IF_DEBUG };

std::atomic_bool Util::Err::Claricpp::append_backtrace { false };

void Util::Err::Claricpp::log_atomic_change(CCSC what, const bool old, const bool new_) noexcept {
    const constexpr auto str { [](const bool b) { return b ? "enabled" : "disabled"; } };
    try {
        Util::Log::info("Util::Err::Claricpp: ", what, " changed from ", str(old), " to ",
                        str(new_));
    }
    catch (std::exception &e) {
        Util::fallback_error_log("Util::Err::Claricpp: ", false);
        Util::fallback_error_log(what, false);
        Util::fallback_error_log(" changed from ");
        Util::fallback_error_log(old ? "true" : "false", false);
        Util::fallback_error_log(" to ", false);
        Util::fallback_error_log(new_ ? "true" : "false");
        Util::fallback_error_log("Log failure! Fallback log was used. Log exception: ", false);
        Util::fallback_error_log(e.what());
    }
}

void Util::Err::Claricpp::warn_backtrace_slow() noexcept {
    static constexpr CCSC msg {
        "Backtraces enabled; claricpp exceptions will generate a backtrace on creation! This will "
        "slow down the program whenever exceptions are created!"
    };
    try {
        Util::Log::warning("Util::Err::Claricpp: ", msg);
    }
    catch (std::exception &e) {
        Util::fallback_error_log("Util::Err::Claricpp: ", false);
        Util::fallback_error_log(msg);
        Util::fallback_error_log("Log failure! Fallback log was used. Log exception: ", false);
        Util::fallback_error_log(e.what());
    }
}

std::ostringstream Util::Err::Claricpp::save_backtrace() noexcept {
    std::ostringstream o;
    if (backtraces_enabled()) {
        ::Util::Backtrace::backward(o, frame_offset); // Prefer 'backward' over 'native'
    }
    else {
        o << "Backtraces are disabled.";
    }
    return o; // Copy elision or compile error :)
}
