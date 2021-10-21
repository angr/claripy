/** @file */
#include "base.hpp"

#include "../op.hpp"


void Expr::Base::ctor_debug_checks() const {
    using E = Util::Err::Usage;
    if (op->cuid == Op::Symbol::static_cuid) {
        Util::affirm<E>(symbolic, WHOAMI_HEADER_ONLY "Symbolic Op may not be concrete");
    }
    else if (op->cuid == Op::Literal::static_cuid) {
        Util::affirm<E>(!symbolic, WHOAMI_HEADER_ONLY "Literal Op may not be symbolic");
    }
}
