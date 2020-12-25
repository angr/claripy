/** @file */
#include "vs.hpp"

#include "../../utils/inc.hpp"


// Define required AST functions
AST_RAWTYPES_DEFINE_AST_SUBBITS_ID_FUNCTIONS(VS)


// For clarity
using namespace AST;


/** @todo */
RawTypes::VS::VS(const Hash h, const Ops::Operation o) : RawTypes::Bits(h, o, 0) {}

/** @todo make this actually work */
Hash RawTypes::VS::hash(const Ops::Operation o) {
    return Hash(VS::static_class_id) * (1 + Hash(o));
}
