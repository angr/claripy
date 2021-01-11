/** @file */
#include "if.hpp"


// For brevity
using namespace Expression::Raw;
using namespace Op;


If::~If() {}

If::If(const Expression::Bool &c, const Expression::Base &if_t, const Expression::Base &if_f)
    : cond(c), if_true(if_t), if_false(if_f) {}

Constants::CCS If::op() const {
    return "If";
}
