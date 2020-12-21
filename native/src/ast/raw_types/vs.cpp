/** @file */
#include "vs.hpp"

#include "../../utils/inc.hpp"


// Define required AST functions
DEFINE_AST_SUBBITS_ID_FUNCTIONS(VS)


// For clarity
using namespace AST;


/** @todo */
RawTypes::VS::VS(const Hash h, const Ops::Operation o) : RawTypes::Bits(h, o, 0) {}
