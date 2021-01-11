/** @file */
#include "literal.hpp"


// For brevity
using namespace Expression::Raw;
using namespace Op;


Literal::~Literal() {}

Literal::Literal(const Constants::Int v) : value(v) {}

Constants::CCS Literal::op() const {
    return "Literal";
}
