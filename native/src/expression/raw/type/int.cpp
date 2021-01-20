/** @file */
#include "int.hpp"


// For clarity
using namespace Expression::Raw;
using namespace Type;


Int::~Int() {}

Constants::CCS Int::type() const {
    return "Int";
}
