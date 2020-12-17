/** @file */
#include "int.hpp"


// Return the name of the type this class represents
std::string AST::Cached::Int::type_name() const {
    return "AST::Int";
}

/** @todo make this actually work */
AST::Hash AST::Cached::Int::hash(const Ops::Operation o, const Constants::Int length) {
    return Hash(o);
}
