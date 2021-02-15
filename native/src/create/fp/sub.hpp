/**
 * @file
 * @brief This file defines a method to create an Expression with an FP::sub Op
 */
#ifndef __CREATE_FP_SUB_HPP__
#define __CREATE_FP_SUB_HPP__

#include "../private/mode_binary.hpp"


namespace Create::FP {

    /** Create a Expression with an sub op */
    EBasePtr sub(EAnVec &&av, const Expression::BasePtr &left, const Expression::BasePtr &right,
                 const Mode::FP mode) {
        return Private::mode_binary<Op::FP::Sub, Private::SizeMode::First>(
            std::forward<EAnVec>(av), left, right, mode);
    }

} // namespace Create::FP

#endif
