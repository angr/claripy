/**
 * @file
 * @brief This file defines the Expression::Raw::Type::String class
 */
#ifndef __EXPRESSION_RAW_TYPE_STRING_HPP__
#define __EXPRESSION_RAW_TYPE_STRING_HPP__

#include "bits.hpp"


namespace Expression::Raw::Type {

    /** An Expression representing a string */
    class String : virtual public Bits {
        EXPRESSION_RAW_INIT(String)
      public:
        /** Get the type of the expression */
        Constants::CCS type() const override final;

      protected:
        /** A protected constructor to disallow public creation */
        String() = default;
    };

} // namespace Expression::Raw::Type

#endif
