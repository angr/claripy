/** @file */
#include "fp.hpp"

#include "../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBITS_ID_FUNCTIONS(FP)


// For brevity
using namespace Expression;


Raw::Type::FP::~FP() {}

/** @todo */
Raw::Type::FP::FP(const Hash h) : Raw::Type::Bits(h, 0) {}

/** @todo make this actually work */
Hash Raw::Type::FP::hash() {
    return Hash(FP::static_class_id);
}
