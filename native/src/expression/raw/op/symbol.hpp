/**
 * @file
 * @brief The expression representing a Symbol
 */
#ifndef __EXPRESSION_RAW_OP_SYMBOL_HPP__
#define __EXPRESSION_RAW_OP_SYMBOL_HPP__

#include "base.hpp"


namespace Expression::Raw::Op {

    /** The op class Symbol */
    class Symbol : virtual public Base {
        EXPRESSION_RAW_ABSTRACT_INIT_CUSTOM_CTOR(Symbol)
      public:
        /** Return the op */
        Constants::CCS op() const override final;

        /** Symbol name */
        const std::string name;

      protected:
        /** A protected constructor to disallow public creation */
        Symbol(const std::string &name);
    };

} // namespace Expression::Raw::Op

#endif
