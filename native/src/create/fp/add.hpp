/**
 * @file
 * @brief This file defines a method to create an Expression with an FP::Add Op
 */
#ifndef __CREATE_FP_ADD_HPP__
#define __CREATE_FP_ADD_HPP__

#include "../private/mode_binary.hpp"


namespace Create::FP {

    /** Create a Expression with an Add op */
    EBasePtr add(EAnVec &&av, const Expression::BasePtr &left, const Expression::BasePtr &right,
                 const Mode::FP mode) {
        return Private::mode_binary<Op::FP::Add, Private::SizeMode::First>(
            std::forward<EAnVec>(av), left, right, mode);
    }

} // namespace Create::FP

#endif
