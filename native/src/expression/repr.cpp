/** @file */
#include "repr.hpp"

#include "bits.hpp"
#include "type_name.hpp"

#include "../op.hpp"

#include <sstream>


void Expression::repr(const Expression::RawPtr e, std::ostream &out, const bool verbose) {
    Utils::affirm<Utils::Error::Unexpected::NotSupported>(!verbose,
                                                          "verbose repr not yet implemented");
    UTILS_AFFIRM_NOT_NULL_DEBUG(e);
    UTILS_AFFIRM_NOT_NULL_DEBUG(e->op); // Sanity check
    // Null check
    if (e == nullptr) {
        Utils::Log::warning(WHOAMI_WITH_SOURCE "called on nullptr");
        out << R"|({ "ptr":"nullptr" })|";
        return;
    }
    // Normal operation
    out << R"|({ "type":")|" << Expression::type_name(e) << R"|(", "symbolic":)|" << std::boolalpha
        << e->symbolic << ", ";
    if (dynamic_cast<Constants::CTSC<Expression::Bits>>(e) != nullptr) {
        out << R"|("bit_length":)|" << Expression::get_bit_length(e) << ", ";
    }
    out << R"|("op":)|";
    e->op->repr(out, verbose);
    out << " }";
}
