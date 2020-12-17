/** @file */
#include "bv.hpp"


// Return the name of the type this class represents
std::string AST::Cached::BV::fundamental_type_name() const {
    return "AST::BV";
}

/** @todo make this actually work */
AST::Hash AST::Cached::BV::hash(const Ops::Operation o, const Constants::Int length) {
    return Hash(o);
}
