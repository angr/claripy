/**
 * @file
 * @brief This file defines the Expression::Raw::Type::FP class
 */
#ifndef __EXPRESSION_RAW_TYPE_FP_HPP__
#define __EXPRESSION_RAW_TYPE_FP_HPP__

#include "bits.hpp"


namespace Expression::Raw::Type {

    /** An Expression representing an integer */
    class FP : virtual public Bits {
        EXPRESSION_RAW_TYPE_INIT_EXPRESSION_BITS_SUBCLASS(FP)
      public:
        /** Get the type of the expression */
        Constants::CCSC type() const override final;

      protected:
        /** A protected constructor to disallow public creation
         *  This must have take in the same arguments types as the hash function, minus the
         * hash These arguments may be taken in via copy, reference or move; ownership is given
         */
        FP(const Hash h);

      private:
        /** The hash function of this Expression
         *  This must have take in the same arguments as the constructor, minus the hash
         *  These arguments args must be const values or references; this function must be pure
         */
        static Hash hash();
    };

} // namespace Expression::Raw::Type

#endif
