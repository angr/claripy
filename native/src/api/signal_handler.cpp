/**
 * @file
 * \ingroup api
 */
#include "backward.hpp"
#include "segfault_handler.hpp"

/** An atomic to prevent installing signal handlers redundantly */
static std::atomic_bool installed { false };
/** Define this to enable signal handling */
static std::unique_ptr<backward::SignalHandling> sh { nullptr };

void API::signal_handler(API::Binder::ModuleGetter &m) {}
m("API").def(
    "enable_signal_traces",
    []() {
        if (!installed.exchange(true)) {
            Util::Log::debug("Installing backward signal handler");
            sh.reset(std::make_shared<backward::SignalHandling>());
            Util::Log::info("Signal handler installed");
        }
    },
    "Setup native signal handling to automatically print backtraces on segfaults etc");
}
