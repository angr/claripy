/**
 * @file
 * @brief This file defines the Expression::Raw::Type::Bits class
 */
#ifndef __EXPRESSION_RAW_TYPE_BITS_HPP__
#define __EXPRESSION_RAW_TYPE_BITS_HPP__

#include "base.hpp"
#include "../cusized.hpp"


namespace Expression::Raw::Type {

    /** This class represents an Expression of bits */
    class Bits : virtual public Base, virtual public CUSized {
        EXPRESSION_RAW_ABSTRACT_INIT(Bits)
	protected:
        /** A protected constructor to disallow public creation */
        Bits() = default;
    };

} // namespace Expression::Raw::Type

#endif
