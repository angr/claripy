/** @file */
#include "bool.hpp"

#include "../../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBASE_ID_FUNCTIONS(Bool)


// For clarity
using namespace Expression;


Raw::Type::Bool::~Bool() {}

/** @todo finish */
Raw::Type::Bool::Bool(const Expression::Hash h) : Raw::Type::Base(h) {}

/** @todo this is a dummy */
bool Raw::Type::Bool::is_true() const {
    return true;
}

/** @todo this is a dummy */
bool Raw::Type::Bool::is_false() const {
    return true;
}

/** @todo make this actually work */
Hash Raw::Type::Bool::hash() {
    return Hash(Bool::static_class_id);
}
