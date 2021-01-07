/**
 * @file
 * @brief This file defines the Expression::Raw::Type::Bool class
 */
#ifndef __EXPRESSION_RAW_TYPE_BOOL_HPP__
#define __EXPRESSION_RAW_TYPE_BOOL_HPP__

#include "base.hpp"


namespace Expression::Raw::Type {

    /** This class represents an Expression boolean */
    class Bool : public Base {
        EXPRESSION_RAW_TYPE_INIT_EXPRESSION_BASE_SUBCLASS(Bool)
      public:
        /** Return true if the Expression evaluates to true */
        bool is_true() const;

        /** Return true if the Expression evaluates to false */
        bool is_false() const;

      protected:
        /** A protected constructor to disallow public creation
         *  This must have take in the same arguments types as the hash function, minus the
         * hash These arguments may be taken in via copy, reference or move; ownership is given
         */
        Bool(const Hash h);

      private:
        /** The hash function of this Expression
         *  This must have take in the same arguments as the constructor, minus the hash
         *  These arguments args must be const values or references; this function must be pure
         */
        static Hash hash();
    };

} // namespace Expression::Raw::Type

#endif
