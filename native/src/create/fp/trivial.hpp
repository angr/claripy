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

    /** Create a Expr with an FP::ToIEEEBV op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr to_ieee_bv(const EBasePtr &x, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::unary<Ex::BV, Ex::FP, Op::FP::ToIEEEBV, Ex::FP>(x, std::move(sp));
    }

    /********************************************************************/
    /*                 ModeBinary Passthrough Functions                 */
    /********************************************************************/

/** A local macro used for fp mode binary math ops with size mode first */
#define FP_MB_SMF_ARITH(FN, OP)                                                                   \
    inline EBasePtr FN(const EBasePtr &left, const EBasePtr &right,                               \
                       const Mode::FP::Rounding mode, Annotation::SPAV &&sp = nullptr) {          \
        return Private::mode_binary<Op::FP::OP, Private::SizeMode::First>(left, right, mode,      \
                                                                          std::move(sp));         \
    }

    /** Create a Expr with an FP::Add op
     *  Expr pointers may not be nullptr
     */
    FP_MB_SMF_ARITH(add, Add);
    /** Create a Expr with an FP::Sub op
     *  Expr pointers may not be nullptr
     */
    FP_MB_SMF_ARITH(sub, Sub);
    /** Create a Expr with an FP::Mul op
     *  Expr pointers may not be nullptr
     */
    FP_MB_SMF_ARITH(mul, Mul);
    /** Create a Expr with an FP::Div op
     *  Expr pointers may not be nullptr
     */
    FP_MB_SMF_ARITH(div, Div);

    // Cleanup
#undef FP_MB_SMF_ARITH

    /********************************************************************/
    /*                  Ternary Passthrough Functions                   */
    /********************************************************************/

    /** Create an Expr with an FP::FP op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr fp(const EBasePtr &first, const EBasePtr &second, const EBasePtr &third,
                       Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::ternary<Ex::FP, Ex::BV, Op::FP::FP, Private::SizeMode::Add, Ex::BV>(
            first, second, third, std::move(sp));
    }

} // namespace Create::FP

#endif
