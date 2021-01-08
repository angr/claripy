/** @file */
#include "bv.hpp"

#include "../../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBITS_ID_FUNCTIONS(BV)


// For clarity
using namespace Expression::Raw;
using namespace Type;


BV::~BV() {}

/** @todo */
BV::BV(const Hash h) : Bits(h, 0) {}

/** Get the type of the expression */
Constants::CCSC BV::type() const {
    return "BV";
}
