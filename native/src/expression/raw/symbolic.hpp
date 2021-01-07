/**
 * @file
 * @brief
 */
#ifndef __EXPRESSION_RAW_SYMBOLIC_HPP__
#define __EXPRESSION_RAW_SYMBOLIC_HPP__

#include "base.hpp"


namespace Expression::Raw {

    struct Symbolic : virtual public Base {
        virtual ~Symbolic() = 0;
    };

} // namespace Expression::Raw

#endif
