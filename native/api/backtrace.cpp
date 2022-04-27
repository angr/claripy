/**
 * @file
 * \ingroup api
 */
#include "backtrace.hpp"

#include <src/util.hpp>


void API::backtrace(API::Binder::ModuleGetter &m) {
    m("API").def(
        "add_source_root", Util::Backtrace::add_source_root,
        "Set location for backtraces to look for C++ code in; this allows backtraces to"
        "include C++ code snippets in them. Likely this should be passed the native directory.",
        pybind11::arg("native_dir"));
}