/**
 * @file
 * @brief This file defines a method to create an Expression with an Invert Op
 */
#ifndef __CREATE_INVERT_HPP__
#define __CREATE_INVERT_HPP__

#include "private/unary.hpp"


namespace Create {

    /** Create a Expression with an invert op */
    template <typename T> EBasePtr invert(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<T, Op::Invert, Ex::BV, Ex::Bool>(std::forward<EAnVec>(av), x);
    }

} // namespace Create


#endif
