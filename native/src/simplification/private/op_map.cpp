/** @file */
#include "op_map.hpp"

#include "../simplifiers.hpp"


// For clarity
using OP = Op::Operation;
using namespace Simplification;
using namespace Simplification::Simplifier;


/** @todo implement the rest of the simplifiers */
const std::map<OP, SimplifierFunc &> Private::op_map {
    { OP::Reverse, BV::reverse },
    { OP::And, Boolean::and_ },
    { OP::Or, Boolean::or_ },
    { OP::Not, Boolean::not_ },
    /* { OP::Extract, extract }, */
    { OP::Concat, concat },
    { OP::If, if_ },
    { OP::__lshift__, Shift::l },
    { OP::__rshift__, Shift::r },
    { OP::LShR, Shift::lshr },
    { OP::__eq__, eq },
    { OP::__ne__, ne },
    { OP::__or__, Bitwise::or_ },
    { OP::__and__, Bitwise::and_ },
    { OP::__xor__, Bitwise::xor_ },
    { OP::__add__, Bitwise::add },
    { OP::__sub__, Bitwise::sub },
    { OP::__mul__, Bitwise::mul },
    /* { OP::ZeroExt, zeroext }, */
    /* { OP::SignExt, signext }, */
    /* { OP::fpToIEEEBV, fptobv }, */
    /* { OP::fpToFP, fptofp }, */
    /* { OP::StrExtract, String::extract }, */
    /* { OP::StrReverse, String::reverse }, */
};
