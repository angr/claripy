/**
 * @file
 * @brief This file defines a method to create an Expression with an Neg Op
 */
#ifndef __CREATE_NEG_HPP__
#define __CREATE_NEG_HPP__

#include "private/unary.hpp"


namespace Create {

    /** Create a Expression with an neg op */
    template <typename T> EBasePtr neg(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<T, Op::Neg, Ex::BV, Ex::FP>(std::forward<EAnVec>(av), x);
    }

} // namespace Create

#endif
