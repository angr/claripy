/** @file */
#include "bv.hpp"

#include "../../../utils.hpp"


// For clarity
using namespace Expression::Raw;
using namespace Type;


BV::~BV() {}

Constants::CCS BV::type() const {
    return "BV";
}
