/** @file */
#include "if.hpp"


// For brevity
using namespace Expression::Raw;
using namespace Op;


If::~If() {}

Constants::CCSC If::op() const {
    return "If";
}
