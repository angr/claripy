#include "log.hpp"

#include "../util.hpp"

#include <pybind11/functional.h>


namespace API {
    /** The python log backend */
    struct PythonLog final : public Util::Log::Backend::Base {
      private:
        /** For brevity */
        using Lvl = ::Util::Log::Level::Level;

      public:
        /** The log function type */
        using Func = std::function<void(CCSC, std::underlying_type_t<Lvl>, std::string)>;
        /** Constructor */
        PythonLog(const Func &log_func) : py_log(log_func) {}
        /** Backend name */
        const char *name() const noexcept final { return "PythonLog"; }
        /** Log the given message */
        void log(CCSC id, const Lvl &lvl, Util::LazyStr &&msg) const final {
            py_log(id, Util::to_underlying(lvl), msg());
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
} // namespace API

void API::bind_log_init(Binder::ModuleGetter &m) {
    m("API").def(
        "install_logger",
        [](const PythonLog::Func &py_log) { Util::Log::Backend::set<PythonLog>(py_log); },
        "Installs log_func to Claricpp's logger. The function "
        "will be called as py_log(id: str, level: int, msg: str)",
        pybind11::arg("py_log"));
    m("API").def(
        "set_log_propagation_level",
        [](const unsigned lvl) {
            Util::Log::Level::set(static_cast<Util::Log::Level::Level>(lvl));
        },
        "Installs log_func to Claricpp's logger. The function "
        "will be called as py_log(id: str, level: int, msg: str)",
        pybind11::arg("py_log"));
}
