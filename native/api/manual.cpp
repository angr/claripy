/**
 * @file
 * \ingroup api
 */
#include "manual.hpp"

#include "backtrace.hpp"
#include "exceptions.hpp"
#include "globals.hpp"
#include "log.hpp"
#include "py_obj.hpp"
#include "signal_handler.hpp"
#include "simplify.hpp"

#include <src/util.hpp>


/** Safely log a message */
static inline void slog(CCSC msg) noexcept try { Util::Log::info(msg); }
UTIL_FALLBACKLOG_CATCH("Logging failed. Original message: ", msg, "\nLogging failed");


void API::bind_manual(pybind11::module_ &root_module, Binder::ModuleGetter &m) {
    register_at_exit([]() noexcept { slog("C++/python decoupled; finalizers now safe to run"); });
    // Custom bindings
    exceptions(root_module);
    signal_handler(m);
    backtrace(m);
    simplify(m);
    globals(m);
    py_obj(m);
    logger(m);
    // Goodbye message
    register_at_exit([]() noexcept { slog("Running C++ exit functions to decouple from python"); });
}