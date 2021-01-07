/** @file */
#include "base.hpp"

#include "../../../utils.hpp"

#include <cstdlib>


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBASE_ID_FUNCTIONS(Base)


// For clarity
using namespace Expression;

/** @todo : maybe delete from hash cache if unique */
Raw::Type::Base::~Base() {}

Hash Raw::Type::Base::hash() {
    return Hash(Base::static_class_id);
}

Raw::Type::Base::Base(const Hash h) : id(h) {}

// Returns a string representation of this
/** @todo: implement rest of repr */
std::string Raw::Type::Base::repr(const bool inner, const Constants::Int max_depth,
                                  const bool explicit_length) const {
    (void) inner;
    (void) max_depth;
    (void) explicit_length;
    if (std::getenv("WORKER") == nullptr) {
        return "<Expression something>";
    }
    else {
        /* return this->shallow_repr(inner, max_depth, explicit_length); */
        return "TODO";
    }
}
