/** @file */
#include "bv.hpp"

#include "../../utils/inc.hpp"


// Define required AST functions
AST_RAWTYPES_DEFINE_AST_SUBBITS_ID_FUNCTIONS(BV)


// For clarity
using namespace AST;


/** @todo */
RawTypes::BV::BV(const Hash h, const Op::Operation o) : RawTypes::Bits(h, o, 0) {}

/** @todo make this actually work */
Hash RawTypes::BV::hash(const Op::Operation o) {
    return Hash(BV::static_class_id) * (1 + Hash(o));
}
