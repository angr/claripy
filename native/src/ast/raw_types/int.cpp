/** @file */
#include "int.hpp"


// For clarity
using namespace AST;


/** @todo finish */
RawTypes::Int::Int(const AST::Hash h, const Ops::Operation o) : RawTypes::Base(h, o) {}

// Return the name of the type this class represents
std::string RawTypes::Int::type_name() const {
    return "AST::Int";
}

/** @todo make this actually work */
AST::Hash RawTypes::Int::hash(const Ops::Operation o) {
    return Hash(o);
}
