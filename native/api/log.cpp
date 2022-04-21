/**
 * @file
 * \ingroup api
 */
#include "log.hpp"

#include <pybind11/functional.h>
#include <src/util.hpp>


/** The python log backend */
struct PythonLog final : public Util::Log::Backend::Base {
  private:
    /** For brevity */
    using Lvl = ::Util::Log::Level::Lvl;

  public:
    /** The log function type */
    using Func = std::function<void(CCSC, Lvl::Raw, std::string)>;
    /** Constructor */
    PythonLog(const Func &log_func) : py_log(log_func) {}
    /** Backend name */
    const char *name() const noexcept final { return "PythonLog"; }
    /** Log the given message */
    void log(CCSC id, const Lvl lvl, Util::LazyStr &&msg) const final {
        py_log(id, lvl.lvl, msg());
    }
    /** Flush the log if applicable
     *  We choose to leave this to python
     */
    void flush() const final {}
    /** The python logging function
     *  Note: we choose to store a reference in case pybind11 cleans up internally on shutdown
     */
    const Func py_log;
};

/** Restore the C++ log backend */
static void set_log_default() noexcept try {
    Util::Log::Backend::set<Util::Log::Backend::Default>();
}
UTIL_FALLBACKLOG_CATCH("Failed to restore C++ default logger")

void API::logger(Binder::ModuleGetter &m) {
    register_at_exit(set_log_default);
    m("API").def(
        "install_logger",
        [](const PythonLog::Func &py_log) { Util::Log::Backend::set<PythonLog>(py_log); },
        "Installs log_func to Claricpp's logger. The function "
        "will be called as py_log(id: str, level: int, msg: str)",
        pybind11::arg("py_log"));
    m("API").def(
        "get_log_level", []() { return Util::Log::Level::get().lvl; }, "Get Claricpp's log level.");
#ifndef CONSTANT_LOG_LEVEL
    m("API").def(
        "set_log_level",
        [](const Util::Log::Level::Lvl::Raw lvl) {
            (TRUE_IF_DEBUG ? Util::Log::Level::set : Util::Log::Level::silent_set)({ lvl });
        },
        "Set the level Claricpp's log level. When a python logger is installed this functionally "
        "defines the minimum log level at which Claricpp will generate a log message and send it "
        "to python's logger.",
        pybind11::arg("lvl"));
#endif
}
