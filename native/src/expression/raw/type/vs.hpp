/**
 * @file
 * @brief This file defines the Expression::Raw::Type::VS class
 */
#ifndef __EXPRESSION_RAW_TYPE_VS_HPP__
#define __EXPRESSION_RAW_TYPE_VS_HPP__

#include "bits.hpp"


namespace Expression::Raw::Type {

    /** An Expression representing a value set */
    class VS : virtual public Bits {
        EXPRESSION_RAW_ABSTRACT_INIT(VS)
      public:
        /** Get the type of the expression */
        Constants::CCS type() const override final;

      protected:
        /** A protected constructor to disallow public creation */
        VS() = default;
    };

} // namespace Expression::Raw::Type

#endif
