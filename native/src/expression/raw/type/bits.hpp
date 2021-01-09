/**
 * @file
 * @brief This file defines the Expression::Raw::Type::Bits class
 */
#ifndef __EXPRESSION_RAW_TYPE_BITS_HPP__
#define __EXPRESSION_RAW_TYPE_BITS_HPP__

#include "base.hpp"


namespace Expression::Raw::Type {

    /** This class represents an Expression of bits */
    class Bits : virtual public Base {
        EXPRESSION_RAW_ABSTRACT_INIT(Bits)
      public:
        /** The number of bits being represented */
        const Constants::Int length;

      protected:
        /* Delete default constructor */
        Bits() = delete;

        /** A protected constructor to disallow public creation */
        Bits(const Constants::Int length);
    };

} // namespace Expression::Raw::Type

#endif
