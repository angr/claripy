/** @file */
#include "int.hpp"

#include "../../utils/inc.hpp"


// Define required AST functions
AST_RAWTYPES_DEFINE_AST_SUBBASE_ID_FUNCTIONS(Int)


// For clarity
using namespace AST;


/** @todo finish */
RawTypes::Int::Int(const AST::Hash h, const Op::Operation o) : RawTypes::Base(h, o) {}

/** @todo make this actually work */
AST::Hash RawTypes::Int::hash(const Op::Operation o) {
    return Hash(Int::static_class_id) * (1 + Hash(o));
}
