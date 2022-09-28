/**
 * @file
 * @brief This file defines a group of fp create methods that are trivial passthrough methods
 * For example: Functions which just shell out to mode_binary
 */
#ifndef R_SRC_CREATE_FP_TRIVIAL_HPP_
#define R_SRC_CREATE_FP_TRIVIAL_HPP_

#include "../private/binary.hpp"
#include "../private/mode_binary.hpp"
#include "../private/ternary.hpp"
#include "../private/unary.hpp"


namespace Create::FP {

    /********************************************************************/
    /*                   Unary Passthrough Functions                    */
    /********************************************************************/

    /** Create a Expr with an FP::IsNan op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr is_nan(const Expr::BasePtr &x, Expr::OpPyDict d = {}) {
        return Private::unary_explicit<Expr::Bool, Op::FP::IsNan, Expr::FP>(x, std::move(d));
    }

    /** Create a Expr with an FP::ToIEEEBV op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr to_ieee_bv(const Expr::BasePtr &x, Expr::OpPyDict d = {}) {
        return Private::unary_explicit<Expr::BV, Op::FP::ToIEEEBV, Expr::FP>(x, std::move(d));
    }

    /********************************************************************/
    /*                 ModeBinary Passthrough Functions                 */
    /********************************************************************/

#define M_FP_MB_SMF_ARITH(FN, OP)                                                                  \
    inline Expr::BasePtr FN(const Expr::BasePtr &left, const Expr::BasePtr &right,                 \
                            const Mode::FP::Rounding mode, Expr::OpPyDict d = {}) {                \
        return Private::mode_binary<Op::FP::OP>(left, right, mode, std::move(d));                  \
    }

    /** Create a Expr with an FP::Add op
     *  Expr pointers may not be nullptr
     */
    M_FP_MB_SMF_ARITH(add, Add);
    /** Create a Expr with an FP::Sub op
     *  Expr pointers may not be nullptr
     */
    M_FP_MB_SMF_ARITH(sub, Sub);
    /** Create a Expr with an FP::Mul op
     *  Expr pointers may not be nullptr
     */
    M_FP_MB_SMF_ARITH(mul, Mul);
    /** Create a Expr with an FP::Div op
     *  Expr pointers may not be nullptr
     */
    M_FP_MB_SMF_ARITH(div, Div);

#undef M_FP_MB_SMF_ARITH

    /********************************************************************/
    /*                  Ternary Passthrough Functions                   */
    /********************************************************************/

    /** Create an Expr with an FP::FP op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr fp(const Expr::BasePtr &first, const Expr::BasePtr &second,
                            const Expr::BasePtr &third, Expr::OpPyDict d = {}) {
        return Private::ternary_explicit<Expr::FP, Op::FP::FP, Expr::BV>(first, second, third,
                                                                         std::move(d));
    }

} // namespace Create::FP

#endif
