/** @file */
#include "fp.hpp"


// Return the name of the type this class represents
std::string AST::Cached::FP::fundamental_type_name() const {
    return "AST::FP";
}

/** @todo make this actually work */
AST::Hash AST::Cached::FP::hash(const Ops::Operation o, const Constants::Int length) {
    return Hash(o);
}
