/** @file */
#include "bits.hpp"

#include "../../../utils.hpp"

#include <sstream>
#include <utility>


// For brevity
using namespace Expression::Raw;
using namespace Type;


Bits::~Bits() {}

Bits::Bits(const Constants::UInt l) : length(l) {}
