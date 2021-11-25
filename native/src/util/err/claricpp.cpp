/**
 * @file
 * \ingroup util
 */
#include "claricpp.hpp"

#include "../backtrace.hpp"
#include "../log.hpp"


std::atomic_bool Util::Err::Claricpp::enable_backtraces { TRUE_IF_DEBUG };

std::atomic_bool Util::Err::Claricpp::append_backtrace { false };

std::ostringstream Util::Err::Claricpp::save_backtrace() noexcept {
    std::ostringstream o;
    if (backtraces_enabled()) {
        ::Util::Backtrace::backward(o, frame_offset);
    }
    return o; // Copy elision or compile error :)
}
