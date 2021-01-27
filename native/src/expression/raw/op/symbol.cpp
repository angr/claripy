/** @file */
#include "symbol.hpp"


// For brevity
using namespace Expression::Raw;
using namespace Op;


Symbol::~Symbol() = default;

Symbol::Symbol(const std::string &n) : name(n) {}

Constants::CCS Symbol::op() const {
    return "Symbol";
}
