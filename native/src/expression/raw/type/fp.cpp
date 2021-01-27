/** @file */
#include "fp.hpp"


// For brevity
using namespace Expression::Raw;
using namespace Type;


FP::~FP() noexcept = default;

Constants::CCS FP::type() const {
    return "FP";
}
