/**
 * @file
 * \ingroup api
 */
#include "signal_handler.hpp"

#include <src/util.hpp>

void API::signal_handler(API::Binder::ModuleGetter &m) {
    m("API").def(
        "enable_signal_traces", []() { Util::Backtrace::handle_signals(); },
        "Setup native signal handling to automatically print backtraces on segfaults etc");
}
