/**
 * @file
 * @brief This file defines a group of fp create methods that are trivial passthrough methods
 * For example: Functions which just shell out to mode_binary
 */
#ifndef R_CREATE_FP_TRIVIAL_HPP_
#define R_CREATE_FP_TRIVIAL_HPP_

#include "../private/binary.hpp"
#include "../private/mode_binary.hpp"
#include "../private/ternary.hpp"
#include "../private/unary.hpp"


namespace Create::FP {

    /********************************************************************/
    /*                   Unary Passthrough Functions                    */
    /********************************************************************/

    /** Create a Expression with an FP::IsInf op */
    inline EBasePtr is_inf(const Expression::BasePtr &x, SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        return Private::unary<Ex::Bool, Ex::FP, Op::FP::IsInf, Ex::FP>(x, std::move(sp));
    }

    /** Create a Expression with an FP::IsNan op */
    inline EBasePtr is_nan(const Expression::BasePtr &x, SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        return Private::unary<Ex::Bool, Ex::FP, Op::FP::IsNaN, Ex::FP>(x, std::move(sp));
    }

    /** Create a Expression with an FP::ToIEEEBV op */
    inline EBasePtr to_ieee_bv(const Expression::BasePtr &x, SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        return Private::unary<Ex::BV, Ex::FP, Op::FP::ToIEEEBV, Ex::FP>(x, std::move(sp));
    }

    /********************************************************************/
    /*                 ModeBinary Passthrough Functions                 */
    /********************************************************************/

/** A local macro used for fp mode binary math ops with size mode first */
#define FP_MB_SMF_ARITH(FN, OP)                                                                   \
    inline EBasePtr FN(const Expression::BasePtr &left, const Expression::BasePtr &right,         \
                       const Mode::FP mode, SPAV &&sp = nullptr) {                                \
        return Private::mode_binary<Op::FP::OP, Private::SizeMode::First>(left, right, mode,      \
                                                                          std::move(sp));         \
    }

    /** Create a Expression with an FP::Add op */
    FP_MB_SMF_ARITH(add, Add);
    /** Create a Expression with an FP::Sub op */
    FP_MB_SMF_ARITH(sub, Sub);
    /** Create a Expression with an FP::Mul op */
    FP_MB_SMF_ARITH(mul, Mul);
    /** Create a Expression with an FP::Div op */
    FP_MB_SMF_ARITH(div, Div);

    // Cleanup
#undef FP_MB_SMF_ARITH

    /********************************************************************/
    /*                  Ternary Passthrough Functions                   */
    /********************************************************************/

    /** Create an Expression with an FP::FP op */
    inline EBasePtr fp(const EBasePtr &first, const EBasePtr &second, const EBasePtr &third,
                       SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        return Private::ternary<Ex::FP, Ex::BV, Op::FP::FP, Private::SizeMode::Add, Ex::BV>(
            first, second, third, std::move(sp));
    }

} // namespace Create::FP

#endif
