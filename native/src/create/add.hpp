/**
 * @file
 * @brief This file defines a method to create an Expression with an Add Op
 */
#ifndef __CREATE_ADD_HPP__
#define __CREATE_ADD_HPP__

#include "private/flat.hpp"


namespace Create {

    /** Create a Expression with an Add op */
    EBasePtr add(EAnVec &&av, Op::Add::OpContainer &&operands) {
        namespace Ex = Expression;
        using OpC = Op::Add::OpContainer;
        return Private::flat<Ex::BV, Op::Add, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), std::forward<OpC>(operands));
    }

} // namespace Create


#endif
