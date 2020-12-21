/** @file */
#include "bool.hpp"

#include "../../utils/inc.hpp"


// Define required AST functions
DEFINE_AST_SUBBASE_ID_FUNCTIONS(Bool)


// For clarity
using namespace AST;


/** @todo finish */
RawTypes::Bool::Bool(const AST::Hash h, const Ops::Operation o) : RawTypes::Base(h, o) {}

/** @todo this is a dummy */
bool RawTypes::Bool::is_true() const {
    return true;
}

/** @todo this is a dummy */
bool RawTypes::Bool::is_false() const {
    return true;
}

/** @todo make this actually work */
Hash RawTypes::Bool::hash(const Ops::Operation o) {
    return Hash(Bool::static_class_id()) * Hash(o);
}
