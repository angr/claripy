/** @file */
#include "fp.hpp"

#include "../../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBITS_ID_FUNCTIONS(FP)


// For brevity
using namespace Expression;


FP::~FP() {}

/** @todo */
FP::FP(const Hash h) : Bits(h, 0) {}

/** Get the type of the expression */
Constants::CCSC FP::type() const {
    return "FP";
}
