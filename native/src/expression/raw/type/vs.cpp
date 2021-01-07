/** @file */
#include "vs.hpp"

#include "../../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBITS_ID_FUNCTIONS(VS)


// For clarity
using namespace Expression;


Raw::Type::VS::~VS() {}

/** @todo */
Raw::Type::VS::VS(const Hash h) : Raw::Type::Bits(h, 0) {}

/** @todo make this actually work */
Hash Raw::Type::VS::hash() {
    return Hash(VS::static_class_id);
}
