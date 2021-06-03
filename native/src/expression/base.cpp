/** @file */
#include "base.hpp"

#include "../op.hpp"


void Expression::Base::ctor_debug_checks() const {
    using Err = Utils::Error::Unexpected::Usage;
    if (op->cuid == Op::Symbol::static_cuid) {
        Utils::affirm<Err>(symbolic, WHOAMI "Symbolic Op may not be concrete");
    }
    else if (op->cuid == Op::Literal::static_cuid) {
        Utils::affirm<Err>(!symbolic, WHOAMI "Literal Op may not be symbolic");
    }
}
