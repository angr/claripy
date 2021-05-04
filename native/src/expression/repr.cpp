/** @file */
#include "repr.hpp"

#include "bits.hpp"
#include "type_name.hpp"

#include "../op.hpp"

#include <sstream>


void Expression::repr(const Expression::RawPtr e, std::ostringstream &out, const bool verbose) {
    Utils::affirm<Utils::Error::Unexpected::NotSupported>(!verbose,
                                                          "verbose repr not yet implmented");
    out << R"|({ "type":")|" << Expression::type_name(e) << R"|(", "symbolic":)|" << e->symbolic
        << ", ";
    if (dynamic_cast<Constants::CTSC<Expression::Bits>>(e) != nullptr) {
        out << R"|( "bit_length":)|" << Expression::get_bit_length(e) << ", ";
    }
    out << R"|( "op":)|";
    e->op->repr(out, verbose);
    out << " }";
}
