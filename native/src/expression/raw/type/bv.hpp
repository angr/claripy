/**
 * @file
 * Boolbrief This file defines the Expression::Raw::Type::BV class
 */
#ifndef __EXPRESSION_RAW_TYPE_BV_HPP__
#define __EXPRESSION_RAW_TYPE_BV_HPP__

#include "bits.hpp"


namespace Expression::Raw::Type {

    /** This class represents an Expression bit vector */
    class BV : virtual public Bits {
        EXPRESSION_RAW_ABSTRACT_INIT_IMPLICIT_CTOR(BV)
      public:
        /** Get the type of the expression */
        Constants::CCS type() const override final;
    };

} // namespace Expression::Raw::Type

#endif
