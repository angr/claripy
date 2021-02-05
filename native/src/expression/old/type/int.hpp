/**
 * @file
 * @brief This file defines the Expression::Raw::Type::Int class
 */
#ifndef __EXPRESSION_RAW_TYPE_INT_HPP__
#define __EXPRESSION_RAW_TYPE_INT_HPP__

#include "base.hpp"


namespace Expression::Raw::Type {

    /** An Expression representing an integer */
    class Int : virtual public Base {
        EXPRESSION_RAW_ABSTRACT_INIT_IMPLICIT_CTOR(Int)
      public:
        /** Get the type of the expression */
        Constants::CCS type() const override final;
    };

} // namespace Expression::Raw::Type

#endif
