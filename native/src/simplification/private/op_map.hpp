/**
 * @file
 * @brief Define a map from Op::Operations to a Simplifier
 */
#ifndef __SIMPLIFICATION_PRIVATE_OPMAP_HPP__
#define __SIMPLIFICATION_PRIVATE_OPMAP_HPP__

#include "../../op.hpp"
#include "../constants.hpp"

#include <map>


namespace Simplification::Private {

    /** A map which maps operations to a simplifiers that can handle it */
    inline const std::map<Op::Base, SimplifierFunc &> op_map {
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

} // namespace Simplification::Private

#endif
