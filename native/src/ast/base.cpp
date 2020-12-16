/** @file */
#include "base.hpp"

#include <cstdlib>

// For clarity
using namespace AST;


Cached::Base::Base(const Ops::Operation o, const Hash h) : op(o), hash(h) {}

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
