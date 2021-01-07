/** @file */
#include "int.hpp"

#include "../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBASE_ID_FUNCTIONS(Int)


// For clarity
using namespace Expression;


Raw::Type::Int::~Int() {}

/** @todo finish */
Raw::Type::Int::Int(const Expression::Hash h) : Raw::Type::Base(h) {}

/** @todo make this actually work */
Expression::Hash Raw::Type::Int::hash() {
    return Hash(Int::static_class_id);
}
