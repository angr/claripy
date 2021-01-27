/** @file */
#include "vs.hpp"


// For clarity
using namespace Expression::Raw;
using namespace Type;


VS::~VS() noexcept = default;

Constants::CCS VS::type() const {
    return "VS";
}
