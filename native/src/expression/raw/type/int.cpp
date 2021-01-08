/** @file */
#include "int.hpp"

#include "../../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBASE_ID_FUNCTIONS(Int)


// For clarity
using namespace Expression::Raw;
using namespace Type;


Type::Int::~Int() {}

/** @todo finish */
Type::Int::Int(const Hash h) : Base(h) {}

/** Get the type of the expression */
Constants::CCSC Int::type() const {
    return "Int";
}
