/** @file */
#include "repr.hpp"

#include "bits.hpp"
#include "type_name.hpp"

#include "../op.hpp"

#include <sstream>


void Expression::repr(const Expression::RawPtr e, std::ostringstream &out, const bool verbose) {
    Utils::affirm<Utils::Error::Unexpected::NotSupported>(!verbose,
                                                          "verbose repr not yet implmented");
    out << '(' << Expression::type_name(e) << "[" << (e->symbolic ? "symbolic" : "concrete");
    if (e->cuid != Expression::Bool::static_cuid) {
        out << ", bl=" << Expression::get_bit_length(e);
    }
    out << "] ";
    e->op->repr(out, verbose);
    out << ')';
}
