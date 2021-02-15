/**
 * @file
 * @brief This file defines a method to create an Expression with a Reverse Op
 */
#ifndef __CREATE_REVERSE_HPP__
#define __CREATE_REVERSE_HPP__

#include "private/unary.hpp"


namespace Create {

    /** Create a Expression with an reverse op */
    EBasePtr reverse(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<Ex::BV, Op::Neg, Ex::BV>(std::forward<EAnVec>(av), x);
    }

} // namespace Create

#endif
