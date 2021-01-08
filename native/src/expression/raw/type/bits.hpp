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
        EXPRESSION_RAW_INIT(Bits)
      public:
        /** The number of bits being represented */
        const Constants::Int length;

      protected:
        /** This constructor must exist for compilations reasons
         *  It should never be explicitly called, however, and will throw and error
         *  This exists because the diamond problem mandates non-most-derived nodes within a
         * diamond to be capable of invoking a constructor even though only the diamond bottom
         * class will be able to invoke the diamond top base constructor
         */
        Bits();

        /** A protected constructor to disallow public creation */
        Bits(const Constants::Int length);
    };

} // namespace Expression::Raw::Type

#endif
