/** @file */
#include "bv.hpp"

#include "../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBITS_ID_FUNCTIONS(BV)


// For clarity
using namespace Expression;


Raw::Type::BV::~BV() {}

/** @todo */
Raw::Type::BV::BV(const Hash h) : Raw::Type::Bits(h, 0) {}

/** @todo make this actually work */
Hash Raw::Type::BV::hash() {
    return Hash(BV::static_class_id);
}
