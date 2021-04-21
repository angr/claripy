/**
 * @file
 * @brief This file defines a group of fp create methods that are trivial passthrough methods
 * For example: Functions which just shell out to mode_binary
 */
#ifndef __CREATE_FP_TRIVIAL_HPP__
#define __CREATE_FP_TRIVIAL_HPP__

#include "../private/binary.hpp"
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
        return Private::unary<Ex::Bool, Ex::FP, Op::FP::IsInf, Ex::FP>(std::forward<EAnVec>(av),
                                                                       x);
    }

    /** Create a Expression with an FP::IsNan op */
    inline EBasePtr is_nan(EAnVec &&av, const Expression::BasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<Ex::Bool, Ex::FP, Op::FP::IsNaN, Ex::FP>(std::forward<EAnVec>(av),
                                                                       x);
    }

    /** Create a Expression with an FP::ToIEEEBV op */
    inline EBasePtr to_ieee_bv(EAnVec &&av, const Expression::BasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<Ex::BV, Ex::FP, Op::FP::ToIEEEBV, Ex::FP>(std::forward<EAnVec>(av),
                                                                        x);
    }

    /********************************************************************/
    /*                 ModeBinary Passthrough Functions                 */
    /********************************************************************/

/** A local macro used for fp mode binary math ops with size mode first */
#define FP_MB_SMF_ARITH(FN, OP)                                                                   \
    inline EBasePtr FN(EAnVec &&av, const Expression::BasePtr &left,                              \
                       const Expression::BasePtr &right, const Mode::FP mode) {                   \
        return Private::mode_binary<Op::FP::OP, Private::SizeMode::First>(                        \
            std::forward<EAnVec>(av), left, right, mode);                                         \
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
    inline EBasePtr fp(EAnVec &&av, const EBasePtr &first, const EBasePtr &second,
                       const EBasePtr &third) {
        namespace Ex = Expression;
        return Private::ternary<Ex::FP, Ex::BV, Op::FP::FP, Private::SizeMode::Add, Ex::BV>(
            std::forward<EAnVec>(av), first, second, third);
    }

} // namespace Create::FP

#endif
