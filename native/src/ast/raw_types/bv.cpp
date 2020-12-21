/** @file */
#include "bv.hpp"


// For clarity
using namespace AST;


/** @todo */
RawTypes::BV::BV(const Hash h, const Ops::Operation o) : RawTypes::Bits(h, o, 0) {}

// Return the name of the type this class represents
std::string RawTypes::BV::fundamental_type_name() const {
    return "AST::BV";
}

/** @todo make this actually work */
Hash RawTypes::BV::hash(const Ops::Operation o) {
    return Hash(o);
}
