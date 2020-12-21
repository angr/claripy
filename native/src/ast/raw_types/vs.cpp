/** @file */
#include "vs.hpp"

#include "../../utils/inc.hpp"


// Define required AST functions
DEFINE_AST_SUBBITS_ID_FUNCTIONS(VS)


// For clarity
using namespace AST;


/** @todo */
RawTypes::VS::VS(const Hash h, const Ops::Operation o) : RawTypes::Bits(h, o, 0) {}

/** @todo make this actually work */
#include <iostream>
Hash RawTypes::VS::hash(const Ops::Operation o) {
    std::cout << "vs: " << Hash(VS::static_class_id) * Hash(o) << std::endl;
    return Hash(VS::static_class_id) * (1 + Hash(o));
}
