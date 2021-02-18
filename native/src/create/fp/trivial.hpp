/**
 * @file
 * @brief This file defines a group of fp create methods that are trivial passthrough methods
 * For example: Functions which just shell out to mode_binary
 */
#ifndef __CREATE_FP_TRIVIAL_HPP__
#define __CREATE_FP_TRIVIAL_HPP__

#include "../private/mode_binary.hpp"
#include "../private/ternary.hpp"


namespace Create::FP {

    /********************************************************************/
    /*                 ModeBinary Passthrough Functions                 */
    /********************************************************************/

    /** Create a Expression with an Add op */
    inline EBasePtr add(EAnVec &&av, const Expression::BasePtr &left,
                        const Expression::BasePtr &right, const Mode::FP mode) {
        return Private::mode_binary<Op::FP::Add, Private::SizeMode::First>(
            std::forward<EAnVec>(av), left, right, mode);
    }

    /** Create a Expression with an sub op */
    inline EBasePtr sub(EAnVec &&av, const Expression::BasePtr &left,
                        const Expression::BasePtr &right, const Mode::FP mode) {
        return Private::mode_binary<Op::FP::Sub, Private::SizeMode::First>(
            std::forward<EAnVec>(av), left, right, mode);
    }

    /** Create a Expression with an div op */
    inline EBasePtr div(EAnVec &&av, const Expression::BasePtr &left,
                        const Expression::BasePtr &right, const Mode::FP mode) {
        return Private::mode_binary<Op::FP::Div, Private::SizeMode::First>(
            std::forward<EAnVec>(av), left, right, mode);
    }

    /********************************************************************/
    /*                  Ternary Passthrough Functions                   */
    /********************************************************************/

    inline EBasePtr fp(EAnVec &&av, const EBasePtr &first, const EBasePtr &second,
                       const EBasePtr &third) {
        namespace Ex = Expression;
        return Private::ternary<Ex::FP, Ex::BV, Op::FP::FP, Private::SizeMode::Add, Ex::BV>(
            std::forward<EAnVec>(av), first, second, third);
    }

} // namespace Create::FP

#endif
