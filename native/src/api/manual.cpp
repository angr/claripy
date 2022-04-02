#include "manual.hpp"

#include "exceptions.hpp"
#include "log.hpp"
#include "simplify.hpp"


void API::bind_manual(pybind11::module_ &root_module, Binder::ModuleGetter &m) {
    API::bind_exceptions(root_module);
    API::bind_simplify_init(m);
    API::bind_log_init(m);
    // TODO: python operators; this should probably be fixed in python, not C++
}