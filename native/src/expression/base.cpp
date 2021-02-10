/** @file */
#include "base.hpp"

#include "../op.hpp"


void Expression::Base::ctor_debug_checks() const {
    using Err = Utils::Error::Unexpected::IncorrectUsage;
    if (op->cuid == Op::Symbol::static_cuid) {
        Utils::affirm<Err>(symbolic, "Symbolic Op may not be concrete");
    }
    else if (op->cuid == Op::Literal::static_cuid) {
        Utils::affirm<Err>(!symbolic, "Literal Op may not be symbolic");
    }
}
