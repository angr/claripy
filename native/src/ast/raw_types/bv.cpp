/** @file */
#include "bv.hpp"

#include "../../utils/inc.hpp"


// Define required AST functions
DEFINE_AST_SUBBITS_ID_FUNCTIONS(BV)


// For clarity
using namespace AST;


/** @todo */
RawTypes::BV::BV(const Hash h, const Ops::Operation o) : RawTypes::Bits(h, o, 0) {}

/** @todo make this actually work */
Hash RawTypes::BV::hash(const Ops::Operation o) {
    return Hash(o);
}
