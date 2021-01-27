/** @file */
#include "bv.hpp"


// For clarity
using namespace Expression::Raw;
using namespace Type;


BV::~BV() = default;

Constants::CCS BV::type() const {
    return "BV";
}
