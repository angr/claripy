/**
 * @file
 * @brief This file defines the base op expression
 */
#ifndef __EXPRESSION_RAW_OP_BASE_HPP__
#define __EXPRESSION_RAW_OP_BASE_HPP__

#include "../base.hpp"


namespace Expression {
    namespace Raw::Op {

        /** Base operation expression
         *  All op expressions must subclass this
         */
        struct Base : virtual public ::Expression::Raw::Base {
            EXPRESSION_RAW_ABSTRACT_INIT_IMPLICIT_CTOR(Base)
        };

    } // namespace Raw::Op

    /** Declare a special alias for base */
    using AbstractOp = std::shared_ptr<Raw::Op::Base>;

} // namespace Expression

#endif
