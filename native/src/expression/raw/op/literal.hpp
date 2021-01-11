/**
 * @file
 * @brief The expression representing a Literal
 */
#ifndef __EXPRESSION_RAW_OP_LITERAL_HPP__
#define __EXPRESSION_RAW_OP_LITERAL_HPP__

#include "base.hpp"

#include "../concrete.hpp"
#include "../type.hpp"


namespace Expression::Raw::Op {

    /** The op class Literal */
    class Literal : virtual public Base, virtual public Concrete {
        EXPRESSION_RAW_ABSTRACT_INIT(Literal)
      public:
        /** Return the op */
        Constants::CCS op() const override final;

        /** Literal value */
        const Constants::Int value;

      protected:
        /** A protected constructor to disallow public creation */
        Literal(const Constants::Int value);

        /** Delete default constructor */
        Literal() = delete;
    };

} // namespace Expression::Raw::Op

#endif
