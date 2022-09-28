/** @file */
#include "base.hpp"

#include "../op.hpp"


void Expr::Base::ctor_debug_checks() const {
    if (op->cuid == Op::Symbol::static_cuid) {
        UTIL_ASSERT(Util::Err::Usage, symbolic, "Symbolic Op may not be concrete");
    }
    else if (op->cuid == Op::Literal::static_cuid) {
        UTIL_ASSERT(Util::Err::Usage, not symbolic, "Literal Op may not be symbolic");
    }
}

void Expr::Base::repr_stream(std::ostream &out) const {
    UTIL_ASSERT_NOT_NULL_DEBUG(op); // Sanity check
    out << R"|({ "type":")|" << type_name();
    out << R"|(", "symbolic":)|" << std::boolalpha << symbolic << ", ";
    if (const auto *const bits { dynamic_cast<CTSC<Expr::Bits>>(this) }; bits) {
        out << R"|("bit_length":)|" << bits->bit_length << ", ";
    }
    out << R"|("op":)|";
    op->repr_stream(out);
    if (dict) {
        // TODO: make repr() give valid json?
        out << ' ' << static_cast<std::string>(pybind11::repr(dict.value()));
    }
    out << " }";
}