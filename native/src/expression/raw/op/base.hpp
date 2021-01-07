/**
 * @file
 * @brief
 */
#ifndef __EXPRESSION_RAW_OP_BASE_HPP__
#define __EXPRESSION_RAW_OP_BASE_HPP__

#include "../base.hpp"


namespace Expression::Raw::Op {

    struct Base : virtual public ::Expression::Raw::Base {
        virtual ~Base() = 0;
    };

} // namespace Expression::Raw::Op

#endif
