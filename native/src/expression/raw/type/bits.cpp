/** @file */
#include "bits.hpp"

#include "../../../utils.hpp"

#include <sstream>
#include <utility>


// Define class id functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBITS_ID_FUNCTIONS(Bits)


// For brevity
using namespace Expression::Raw;
using namespace Type;


Bits::~Bits() {}

/** @todo */
Bits::Bits(const Hash h, const Constants::Int l) : Base(h), length(l) {}
