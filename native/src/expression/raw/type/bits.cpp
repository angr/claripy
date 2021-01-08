/** @file */
#include "bits.hpp"

#include "../../../utils.hpp"

#include <sstream>
#include <utility>


// For brevity
using namespace Expression::Raw;
using namespace Type;


Bits::~Bits() {}

Bits::Bits()
    : length(0) { EXPRESSION_RAW_ILLEGAL_CTOR("Expression::Raw::Type::Bits") }

      /** @todo */
      Bits::Bits(const Constants::Int l)
    : length(l) {}
