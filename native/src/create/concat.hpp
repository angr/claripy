/**
 * @file
 * @brief This file defines a method to create an Expression with an Concat Op
 */
#ifndef __CREATE_CONCAT_HPP__
#define __CREATE_CONCAT_HPP__

#include "private/binary.hpp"


namespace Create {

    /** Create a Expression with an Concat op */
    template <typename T>
    EBasePtr concat(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<T, Op::Concat, Private::SizeMode::Add, Ex::BV, Ex::String>(
            std::forward<EAnVec>(av), left, right);
    }

} // namespace Create

#endif
