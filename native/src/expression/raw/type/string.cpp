/** @file */
#include "string.hpp"


// For clarity
using namespace Expression::Raw;
using namespace Type;


String::~String() = default;

Constants::CCS String::type() const {
    return "String";
}
