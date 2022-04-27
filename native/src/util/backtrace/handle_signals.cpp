/**
 * @file
 * \ingroup util
 */
#include "handle_signals.hpp"

#include "../log.hpp"

#include <backward.hpp>

void Util::Backtrace::handle_signals() {
    static std::unique_ptr<backward::SignalHandling> sh { nullptr };
    static std::atomic_bool installed { false };
    if (not installed.exchange(true)) {
        Util::Log::debug("Installing backward signal handler");
        sh = std::make_unique<backward::SignalHandling>();
        Util::Log::info("Signal handler installed.");
    }
    else {
        Util::Log::warning("This function has been called before. Doing nothing");
    }
}
