/** @file */
#include "fp.hpp"


// For brevity
using namespace Expression::Raw;
using namespace Type;


FP::~FP() = default;

Constants::CCS FP::type() const {
    return "FP";
}
