/**
 * @file
 * @brief
 */
#ifndef __EXPRESSION_RAW_OP_BASE_HPP__
#define __EXPRESSION_RAW_OP_BASE_HPP__

#include "../base.hpp"


namespace Expression::Raw::Op {

    /** Base operation expression
     *  All op expressions must subclass this
     */
    struct Base : virtual public ::Expression::Raw::Base {
        /** Pure virtual destructor */
        virtual ~Base() = 0;
    };

} // namespace Expression::Raw::Op

#endif
