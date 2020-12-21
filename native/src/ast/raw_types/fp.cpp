/** @file */
#include "fp.hpp"


// For brevity
using namespace AST;


/** @todo */
RawTypes::FP::FP(const Hash h, const Ops::Operation o) : RawTypes::Bits(h, o, 0) {}

// Return the name of the type this class represents
std::string RawTypes::FP::fundamental_type_name() const {
    return "AST::FP";
}

/** @todo make this actually work */
Hash RawTypes::FP::hash(const Ops::Operation o) {
    return Hash(o);
}
