/** @file */
#include "int.hpp"


// Return the name of the type this class represents
std::string AST::RawTypes::Int::type_name() const {
    return "AST::Int";
}

/** @todo make this actually work */
AST::Hash AST::RawTypes::Int::hash(const Ops::Operation o, const Constants::Int length) {
    return Hash(o);
}
