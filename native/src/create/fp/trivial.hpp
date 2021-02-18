/**
 * @file
 * @brief This file defines a group of fp create methods that are trivial passthrough methods
 * For example: Functions which just shell out to mode_binary
 */
#ifndef __CREATE_FP_TRIVIAL_HPP__
#define __CREATE_FP_TRIVIAL_HPP__

#include "../private/mode_binary.hpp"
#include "../private/ternary.hpp"
#include "../private/unary.hpp"


namespace Create::FP {

    /********************************************************************/
    /*                   Unary Passthrough Functions                    */
    /********************************************************************/

    /** Create a Expression with an FP::IsInf op */
    inline EBasePtr is_inf(EAnVec &&av, const Expression::BasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<Ex::Bool, Ex::FP, Op::FP::IsInf, Private::SizeMode::NA, Ex::FP>(
            std::forward<EAnVec>(av), x);
    }

    /** Create a Expression with an FP::IsNan op */
    inline EBasePtr is_nan(EAnVec &&av, const Expression::BasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<Ex::Bool, Ex::FP, Op::FP::IsNaN, Private::SizeMode::NA, Ex::FP>(
            std::forward<EAnVec>(av), x);
    }

    /** Create a Expression with an FP::ToIEEEBV op */
    inline EBasePtr to_ieee_bv(EAnVec &&av, const Expression::BasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<Ex::BV, Ex::FP, Op::FP::ToIEEEBV, Private::SizeMode::First, Ex::FP>(
            std::forward<EAnVec>(av), x);
    }

    /********************************************************************/
    /*                   Binary Passthrough Functions                   */
    /********************************************************************/

    /** Create a Expression with an FP::NE op */
    inline EBasePtr ne(EAnVec &&av, const Expression::BasePtr &left,
                       const Expression::BasePtr &right) {
        namespace Ex = Expression;
        return Private::unary<Ex::Bool, Ex::FP, Op::FP::NE, Private::SizeMode::NA, Ex::FP>(
            std::forward<EAnVec>(av), left, right);
    }

    /********************************************************************/
    /*                 ModeBinary Passthrough Functions                 */
    /********************************************************************/

    /** Create a Expression with an FP::Add op */
    inline EBasePtr add(EAnVec &&av, const Expression::BasePtr &left,
                        const Expression::BasePtr &right, const Mode::FP mode) {
        return Private::mode_binary<Op::FP::Add, Private::SizeMode::First>(
            std::forward<EAnVec>(av), left, right, mode);
    }

    /** Create a Expression with an FP::Sub op */
    inline EBasePtr sub(EAnVec &&av, const Expression::BasePtr &left,
                        const Expression::BasePtr &right, const Mode::FP mode) {
        return Private::mode_binary<Op::FP::Sub, Private::SizeMode::First>(
            std::forward<EAnVec>(av), left, right, mode);
    }

    /** Create a Expression with an FP::Div op */
    inline EBasePtr div(EAnVec &&av, const Expression::BasePtr &left,
                        const Expression::BasePtr &right, const Mode::FP mode) {
        return Private::mode_binary<Op::FP::Div, Private::SizeMode::First>(
            std::forward<EAnVec>(av), left, right, mode);
    }

    /********************************************************************/
    /*                  Ternary Passthrough Functions                   */
    /********************************************************************/

    /** Create an Expression with an FP::FP op */
    inline EBasePtr fp(EAnVec &&av, const EBasePtr &first, const EBasePtr &second,
                       const EBasePtr &third) {
        namespace Ex = Expression;
        return Private::ternary<Ex::FP, Ex::BV, Op::FP::FP, Private::SizeMode::Add, Ex::BV>(
            std::forward<EAnVec>(av), first, second, third);
    }

} // namespace Create::FP

#endif
