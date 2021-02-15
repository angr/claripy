/**
 * @file
 * @brief This file defines a method to create an Expression with an Abs Op
 */
#ifndef __CREATE_ABS_HPP__
#define __CREATE_ABS_HPP__

#include "private/unary.hpp"


namespace Create {

    /** Create a Expression with an abs op */
    template <typename T> EBasePtr abs(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<T, Op::Abs, Ex::BV, Ex::FP>(std::forward<EAnVec>(av), x);
    }

} // namespace Create

#endif
