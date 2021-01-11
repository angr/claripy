/**
 * @file
 * @brief The expression representing an If expression
 */
#ifndef __EXPRESSION_RAW_OP_IF_HPP__
#define __EXPRESSION_RAW_OP_IF_HPP__

#include "base.hpp"

#include "../type.hpp"


namespace Expression::Raw::Op {

    /** The op class If */
    class If : virtual public Base {
        EXPRESSION_RAW_ABSTRACT_INIT(If)
      public:
        /** Return the op */
        Constants::CCS op() const override final;

        /** If condition */
        const Expression::Bool cond;
        /** If true expression */
        const Expression::Base if_true;
        /** If false expression */
        const Expression::Base if_false;

      protected:
        /** Constructor */
        If(const Expression::Bool &cond, const Expression::Base &if_true,
           const Expression::Base &if_false);

        /** Delete default constructor */
        If() = delete;
    };

} // namespace Expression::Raw::Op

#endif
