/**
 * @file
 * @brief This file defines the Expression::Raw::Type::Bool class
 */
#ifndef __EXPRESSION_RAW_TYPE_BOOL_HPP__
#define __EXPRESSION_RAW_TYPE_BOOL_HPP__

#include "base.hpp"


namespace Expression::Raw::Type {

    /** This class represents an Expression boolean */
    class Bool : virtual public Base {
        EXPRESSION_RAW_ABSTRACT_INIT(Bool)
      public:
        /** Return true if the Expression evaluates to true */
        bool is_true() const;

        /** Return true if the Expression evaluates to false */
        bool is_false() const;

        /** Get the type of the expression */
        Constants::CCS type() const override final;

      protected:
        /** A protected constructor to disallow public creation */
        Bool() = default;
    };

} // namespace Expression::Raw::Type

#endif
