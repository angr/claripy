/**
 * @file
 * \ingroup util
 */
#include "claricpp.hpp"

#include "../backtrace.hpp"
#include "../log.hpp"

#ifdef DEBUG

thread_local std::atomic_bool Util::Error::Claricpp::enable_backtraces { false };


void Util::Error::Private::backtrace_if_debug() {
    if (Util::Error::Claricpp::backtraces_enabled()) {
        std::ostringstream s;
        s << "Backtrace:\n";
        Util::backtrace(s, 1);
        Util::Log::error(s.str());
    }
}

#endif
