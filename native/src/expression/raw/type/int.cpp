/** @file */
#include "int.hpp"

#include "../../../utils.hpp"


// For clarity
using namespace Expression::Raw;
using namespace Type;


Int::~Int() {}

Constants::CCSC Int::type() const {
    return "Int";
}
