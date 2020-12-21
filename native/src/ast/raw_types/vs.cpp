/** @file */
#include "vs.hpp"


// For clarity
using namespace AST;


/** @todo */
RawTypes::VS::VS(const Hash h, const Ops::Operation o) : RawTypes::Bits(h, o, 0) {}

// Return the name of the type this class represents
std::string RawTypes::VS::fundamental_type_name() const {
    return "AST::VS";
}

/** @todo make this actually work */
Hash RawTypes::VS::hash(const Ops::Operation o) {
    return Hash(o);
}
