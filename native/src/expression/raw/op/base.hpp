/**
 * @file
 * @brief This file defines the base op expression
 */
#ifndef __EXPRESSION_RAW_OP_BASE_HPP__
#define __EXPRESSION_RAW_OP_BASE_HPP__

#include "../base.hpp"


namespace Expression::Raw::Op {

    /** Base operation expression
     *  All op expressions must subclass this
     */
    struct Base : virtual public ::Expression::Raw::Base {
        EXPRESSION_RAW_INIT(Base)
      protected:
        /** Protected constructor */
        Base();
    };

} // namespace Expression::Raw::Op

#endif
