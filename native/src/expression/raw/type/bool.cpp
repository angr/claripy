/** @file */
#include "bool.hpp"

#include "../../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBASE_ID_FUNCTIONS(Bool)


// For clarity
using namespace Expression::Raw;
using namespace Type;


Bool::~Bool() {}

/** @todo finish */
Bool::Bool(const Hash h) : Base(h) {}

/** @todo this is a dummy */
bool Bool::is_true() const {
    return true;
}

/** @todo this is a dummy */
bool Bool::is_false() const {
    return true;
}

/** Get the type of the expression */
Constants::CCSC Bool::type() const {
    return "Bool";
}
