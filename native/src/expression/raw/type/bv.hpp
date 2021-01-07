/**
 * @file
 * Boolbrief This file defines the Expression::Raw::Type::BV class
 */
#ifndef __EXPRESSION_RAW_TYPE_BV_HPP__
#define __EXPRESSION_RAW_TYPE_BV_HPP__

#include "bits.hpp"


namespace Expression::Raw::Type {

    /** This class represents an Expression bit vector */
    class BV : public Bits {
        EXPRESSION_RAW_TYPE_INIT_EXPRESSION_BITS_SUBCLASS(BV)

      protected:
        /** A protected constructor to disallow public creation
         *  This must have take in the same arguments types as the hash function, minus the
         * hash These arguments may be taken in via copy, reference or move; ownership is given
         */
        BV(const Hash h);

      private:
        /** The hash function of this Expression
         *  This must have take in the same arguments as the constructor, minus the hash
         *  These arguments args must be const values or references; this function must be pure
         */
        static Hash hash();
    };

} // namespace Expression::Raw::Type

#endif
