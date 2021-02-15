/**
 * @file
 * @brief This file defines a method to create an Expression with an sub Op
 */
#ifndef __CREATE_SUB_HPP__
#define __CREATE_SUB_HPP__

#include "constants.hpp"
#include "private/binary.hpp"
#include "private/size.hpp"


namespace Create {

    /** Create a Bool Expression with an sub op */
    EBasePtr sub(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Sub, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

} // namespace Create

#endif
