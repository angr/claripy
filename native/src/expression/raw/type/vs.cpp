/** @file */
#include "vs.hpp"

#include "../../../utils.hpp"


// For clarity
using namespace Expression::Raw;
using namespace Type;


VS::~VS() {}

Constants::CCS VS::type() const {
    return "VS";
}
