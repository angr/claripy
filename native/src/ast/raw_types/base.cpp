/** @file */
#include "base.hpp"

#include "../../utils/inc.hpp"

#include <cstdlib>


// Define required AST functions
DEFINE_AST_SUBBASE_ID_FUNCTIONS(Base)


// For clarity
using namespace AST;

/** @todo : maybe delete from hash cache if unique */
RawTypes::Base::~Base() {}

Hash RawTypes::Base::hash(const Ops::Operation o) {
    return Hash(Base::static_class_id()) * Hash(o);
}

RawTypes::Base::Base(const Hash h, const Ops::Operation o) : id(h), op(o) {}

// Returns a string representation of this
/** @todo: implement rest of repr */
std::string RawTypes::Base::repr(const bool inner, const Constants::Int max_depth,
                                 const bool explicit_length) const {
    (void) inner;
    (void) max_depth;
    (void) explicit_length;
    if (std::getenv("WORKER") == nullptr) {
        return "<AST something>";
    }
    else {
        /* return this->shallow_repr(inner, max_depth, explicit_length); */
        return "TODO";
    }
}
