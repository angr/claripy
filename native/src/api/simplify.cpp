#include "simplify.hpp"

#include "../simplify.hpp"

#include <pybind11/functional.h>


void API::bind_simplify_init(API::Binder::ModuleGetter &m) {
    m("API").def(
        "set_python_simplifier",
        [](const std::function<Simplify::Func> &s) { Simplify::manager.set_python_simplifier(s); },
        "Set a function to be called on every invocation of the builtin simplify()."
        " Will be called as simplifier(op)",
        pybind11::arg("simplifier"));
}