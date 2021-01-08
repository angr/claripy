/** @file */
#include "vs.hpp"

#include "../../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBITS_ID_FUNCTIONS(VS)


// For clarity
using namespace Expression::Raw;
using namespace Type;


VS::~VS() {}

/** @todo */
VS::VS(const Hash h) : Bits(h, 0) {}

/** Get the type of the expression */
Constants::CCSC VS::type() const {
    return "VS";
}
