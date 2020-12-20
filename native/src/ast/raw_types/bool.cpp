/** @file */
#include "bool.hpp"


// For clarity
using namespace AST;


/** @todo this is a dummy */
bool RawTypes::Bool::is_true() const {
    return true;
}

/** @todo this is a dummy */
bool RawTypes::Bool::is_false() const {
    return true;
}

// Return the name of the type this class represents
std::string RawTypes::Bool::type_name() const {
    return "AST::Bool";
}

/** @todo make this actually work */
Hash RawTypes::Bool::hash(const Ops::Operation o, const Constants::Int length) {
    (void) length;
    return Hash(o);
}
