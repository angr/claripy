/**
 * @file
 * @brief This file defines the Expression::Raw::Type::Bits class
 */
#ifndef __EXPRESSION_RAW_TYPE_BITS_HPP__
#define __EXPRESSION_RAW_TYPE_BITS_HPP__

#include "base.hpp"


namespace Expression::Raw::Types {

    /** This class represents an Expression of bits */
    class Bits : public Base {
        EXPRESSION_RAW_TYPE_INIT_EXPRESSION_BASE_SUBCLASS(Bits)
      public:
        EXPRESSION_RAW_TYPE_DECLARE_EXPRESSION_SUBBITS_TYPENAME

        /** The number of bits being represented */
        const Constants::Int length;

      protected:
        /** A protected constructor to disallow public creation
         *  This must have take in the same arguments types as the hash function, minus the
         * hash These arguments may be taken in via copy, reference or move; ownership is given
         */
        Bits(const Hash h, const Constants::Int length);

      private:
        /** The hash function of this Expression
         *  This must have take in the same arguments as the constructor, minus the hash
         *  These arguments args must be const values or references; this function must be pure
         */
        static Hash hash(const Constants::Int length);

        /** Throw an exception if old and new_ are not of the same length @todo static */
        void check_replaceability(const ::Expression::Bits &old, const ::Expression::Bits &new_);
    };

} // namespace Expression::Raw::Types

#endif
