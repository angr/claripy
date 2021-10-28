/**
 * @file
 * \ingroup util
 */
#include "claricpp.hpp"

#include "../backtrace.hpp"
#include "../log.hpp"

#ifdef DEBUG

std::atomic_bool Util::Err::Claricpp::enable_backtraces { false };

std::ostringstream Util::Err::Claricpp::save_backtrace() noexcept {
    if (!backtraces_enabled()) {
        return std::ostringstream {};
    }
    std::ostringstream o;
    o << "Backtrace:\n";
    ::Util::backtrace(o, 1);
    return o; // Copy elision or compile error :)
}

#endif
