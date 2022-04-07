#include "manual.hpp"

#include "exceptions.hpp"
#include "log.hpp"
#include "simplify.hpp"

#include "../util.hpp"


/** Safely log a message */
static inline void slog(CCSC msg) noexcept try { Util::Log::info(msg); }
UTIL_FALLBACKLOG_CATCH("Logging failed. Original message: ", msg, "\nLogging failed");

void API::bind_manual(pybind11::module_ &root_module, Binder::ModuleGetter &m) {
    register_at_exit([]() noexcept {
        slog("C++/python decoupled; finalizers now safe to run");
    }); // TODO: make custom function so orders can be set?
    API::bind_exceptions(root_module);
    API::bind_simplify_init(m);
    API::bind_log_init(m);
    register_at_exit([]() noexcept { slog("Running C++ exit functions to decouple from python"); });
    // TODO: python operators; this should probably be fixed in python, not C++
}
