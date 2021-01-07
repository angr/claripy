/**
 * @file
 * @brief This file defines the Expression::Raw::Type::Int class
 */
#ifndef __EXPRESSION_RAW_TYPE_INT_HPP__
#define __EXPRESSION_RAW_TYPE_INT_HPP__

#include "base.hpp"


namespace Expression::Raw::Type {

    /** An Expression representing an integer */
    class Int : public Base {
        EXPRESSION_RAW_TYPE_INIT_EXPRESSION_BASE_SUBCLASS(Int)

      protected:
        /** A protected constructor to disallow public creation
         *  This must have take in the same arguments types as the hash function, minus the
         * hash These arguments may be taken in via copy, reference or move; ownership is given
         */
        Int(const Hash h);

      private:
        /** The hash function of this Expression
         *  This must have take in the same arguments as the constructor, minus the hash
         *  These arguments args must be const values or references; this function must be pure
         */
        static Hash hash();
    };

} // namespace Expression::Raw::Type

#endif
