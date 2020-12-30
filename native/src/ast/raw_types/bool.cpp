/** @file */
#include "bool.hpp"

#include "../../utils.hpp"


// Define required AST functions
AST_RAWTYPES_DEFINE_AST_SUBBASE_ID_FUNCTIONS(Bool)


// For clarity
using namespace AST;


/** @todo finish */
RawTypes::Bool::Bool(const AST::Hash h, const Op::Operation o) : RawTypes::Base(h, o) {}

/** @todo this is a dummy */
bool RawTypes::Bool::is_true() const {
    return true;
}

/** @todo this is a dummy */
bool RawTypes::Bool::is_false() const {
    return true;
}

/** @todo make this actually work */
Hash RawTypes::Bool::hash(const Op::Operation o) {
    return Hash(Bool::static_class_id) * (1 + Hash(o));
}
