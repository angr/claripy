#include "manual.hpp"

#include "exceptions.hpp"
#include "headers.hpp"
#include "log.hpp"


void API::bind_manual(pybind11::module_ &root_module, Binder::ModuleGetter &m) {
    API::bind_exceptions(root_module);
    API::bind_log_init(m);
    // TODO: hookup simplify (link classes and add + bind some init_simplify() function)
    // TODO: python operators; == should not work as it does!
}