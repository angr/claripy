/** @file */
#include "literal.hpp"


// For brevity
using namespace Expression::Raw;
using namespace Op;


Literal::~Literal() {}

Literal::Literal(Constants::CCSC) : value(0) {}

Constants::CCS Literal::op() const {
    return "Literal";
}
