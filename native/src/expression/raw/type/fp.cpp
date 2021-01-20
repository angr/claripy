/** @file */
#include "fp.hpp"


// For brevity
using namespace Expression::Raw::Type;


FP::~FP() {}

Constants::CCS FP::type() const {
    return "FP";
}
