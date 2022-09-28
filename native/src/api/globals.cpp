/**
 * @file
 * \ingroup api
 */
#include "globals.hpp"

#include "../mode.hpp"


/** Register globals with pybind11 */
void API::globals(API::Binder::ModuleGetter &m) {
    // Pass by value not reference (inlined variables)
    m("Mode::FP").attr("flt") = Mode::FP::flt;
    m("Mode::FP").attr("dbl") = Mode::FP::dbl;
}
