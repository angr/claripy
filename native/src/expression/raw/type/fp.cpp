/** @file */
#include "fp.hpp"

#include "../../../utils.hpp"


// For brevity
using namespace Expression::Raw::Type;


FP::~FP() {}

Constants::CCSC FP::type() const {
    return "FP";
}
