/**
 * @file
 * @brief This file defines many useful using statements within Expression
 * For example, Expression::Base is defined as std::shared_ptr<Expression::Raw::Type::Base>
 * @todo disable shared_ptr.get() ?
 */
#ifndef __EXPRESSION_FORWARD_DECLARATIONS_HPP__
#define __EXPRESSION_FORWARD_DECLARATIONS_HPP__

#include "macros.hpp"

#include <memory>


namespace Expression {

    namespace Raw::Type {
        // Forward declare classes
        class Base;
        class Bool;
        class Bits;
        class String;
        class Int;
        class VS;
        class BV;
    } // namespace Raw::Type

    // Define shared pointer abbreviations
    EXPRESSION_DECLARE_AND_DEFINE_NON_RAW_TYPE(Base)
    EXPRESSION_DECLARE_AND_DEFINE_NON_RAW_TYPE(Bool)
    EXPRESSION_DECLARE_AND_DEFINE_NON_RAW_TYPE(Bits)
    EXPRESSION_DECLARE_AND_DEFINE_NON_RAW_TYPE(BV)
    EXPRESSION_DECLARE_AND_DEFINE_NON_RAW_TYPE(VS)
    EXPRESSION_DECLARE_AND_DEFINE_NON_RAW_TYPE(String)
    EXPRESSION_DECLARE_AND_DEFINE_NON_RAW_TYPE(Int)

} // namespace Expression

#endif
