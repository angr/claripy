/**
 * @file
 * \ingroup utils
 */
#include "claricpp.hpp"

#include "../backtrace.hpp"
#include "../log.hpp"

#ifdef DEBUG

thread_local std::atomic_bool Utils::Error::Claricpp::enable_backtraces { false };


void Utils::Error::Private::backtrace_if_debug() {
    if (Utils::Error::Claricpp::backtraces_enabled()) {
        std::ostringstream s;
        Utils::backtrace(s, 1);
        Utils::Log::error(s.str());
    }
}

#endif
