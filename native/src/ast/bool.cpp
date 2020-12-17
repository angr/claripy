/** @file */
#include "bool.hpp"


// For clarity
using namespace AST;

/** @todo this is a dummy */
bool Cached::Bool::is_true() const {
    return true;
}

/** @todo this is a dummy */
bool Cached::Bool::is_false() const {
    return true;
}

// Return the name of the type this class represents
std::string Cached::Bool::type_name() const {
    return "AST::Bool";
}
