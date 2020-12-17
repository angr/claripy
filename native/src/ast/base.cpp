/** @file */
#include "base.hpp"

#include <cstdlib>

// For clarity
using namespace AST;

/** @todo : maybe delete from hash cache if unique */
Cached::Base::~Base() {}

Hash Cached::Base::hash(const Ops::Operation o) {
    return Hash(o);
}

Cached::Base::Base(const Hash h, const Ops::Operation o) : id(h), op(o) {}

// Returns a string representation of this
/** @todo: implement rest of repr */
std::string Cached::Base::repr(const bool inner, const Constants::Int max_depth,
                               const bool explicit_length) const {
    if (std::getenv("WORKER") == nullptr) {
        return "<AST something>";
    }
    else {
        /* return this->shallow_repr(inner, max_depth, explicit_length); */
        return "TODO";
    }
}

// Return the name of the type this class represents
std::string Cached::Base::type_name() const {
    return "AST::Base";
}
