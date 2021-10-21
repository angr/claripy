/**
 * @file
 * @brief This file defines a group of create methods that are trivial passthrough methods
 * For example: Functions which just shell out to unary, binary, or flat
 */
#ifndef R_CREATE_TRIVIAL_HPP_
#define R_CREATE_TRIVIAL_HPP_

#include "private/binary.hpp"
#include "private/flat.hpp"
#include "private/uint_binary.hpp"
#include "private/unary.hpp"


namespace Create {

    /********************************************************************/
    /*                   Unary Passthrough Functions                    */
    /********************************************************************/

    /** Create an Expr with an Abs op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr abs(const Expr::BasePtr &x, Annotation::SPAV &&sp = nullptr) {
        return Private::unary<Op::Abs, Expr::FP>(x, std::move(sp));
    }

    /** Create an Expr with an Neg op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr neg(const Expr::BasePtr &x, Annotation::SPAV &&sp = nullptr) {
        return Private::unary<Op::Neg, Expr::BV, Expr::FP>(x, std::move(sp));
    }

    /** Create an Expr with an Not op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr not_(const Expr::BasePtr &x, Annotation::SPAV &&sp = nullptr) {
        return Private::unary<Op::Not, Expr::Bool>(x, std::move(sp));
    }

    /** Create an Expr with an Invert op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr invert(const Expr::BasePtr &x, Annotation::SPAV &&sp = nullptr) {
        return Private::unary<Op::Invert, Expr::BV>(x, std::move(sp));
    }

    /** Create an Expr with an Reverse op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr reverse(const Expr::BasePtr &x, Annotation::SPAV &&sp = nullptr) {
        return Private::unary<Op::Reverse, Expr::BV>(x, std::move(sp));
    }

    /********************************************************************/
    /*                UInt Binary Passthrough Functions                 */
    /********************************************************************/

    /** Create an Expr with an SignExt op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr sign_ext(const Expr::BasePtr &expr, const UInt integer,
                                  Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::uint_binary<UInt, Ex::BV, Op::SignExt, Private::SizeMode::Add, Ex::BV>(
            expr, integer, std::move(sp));
    }

    /** Create an Expr with an ZeroExt op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr zero_ext(const Expr::BasePtr &expr, const UInt integer,
                                  Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::uint_binary<UInt, Ex::BV, Op::ZeroExt, Private::SizeMode::Add, Ex::BV>(
            expr, integer, std::move(sp));
    }

    /********************************************************************/
    /*                   Binary Passthrough Functions                   */
    /********************************************************************/

    // Comparisons

    /** Create a Bool Expr with an Eq op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    inline Expr::BasePtr eq(const Expr::BasePtr &left, const Expr::BasePtr &right,
                            Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::Bool, T, Op::Eq, Private::SizeMode::NA, Ex::FP, Ex::Bool,
                               Ex::BV, Ex::String>(left, right, std::move(sp));
    }

    /** Create a Bool Expr with an Neq op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    inline Expr::BasePtr neq(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::Bool, T, Op::Neq, Private::SizeMode::NA, Ex::FP, Ex::Bool,
                               Ex::BV, Ex::String>(left, right, std::move(sp));
    }

    /** Create an Expr with a Compare op
     *  Expr pointers may not be nullptr
     */
    template <typename In, Mode::Compare Mask>
    inline Expr::BasePtr compare(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                 Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        static_assert(Mode::compare_is_valid(Mask), "Invalid Compare Mode");
        static_assert(Util::BitMask::has(Mask, Mode::Compare::Signed) ||
                          !Util::is_same_ignore_const<In, Ex::FP>,
                      "FP comparisons must be signed");
        return Private::binary<Ex::Bool, In, Op::Compare<Mask>, Private::SizeMode::NA, Ex::FP,
                               Ex::BV>(left, right, std::move(sp));
    }

    // Math

    /** Create an Expr with an Sub op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr sub(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Sub, Private::SizeMode::First, Ex::BV>(left, right,
                                                                                  std::move(sp));
    }

    /** Create an Expr with an Div op
     *  Expr pointers may not be nullptr
     */
    template <bool Signed>
    inline Expr::BasePtr div(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Div<Signed>, Private::SizeMode::First, Ex::BV>(
            left, right, std::move(sp));
    }

    /** Create an Expr with an Mod op
     *  Expr pointers may not be nullptr
     */
    template <bool Signed>
    inline Expr::BasePtr mod(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Mod<Signed>, Private::SizeMode::First, Ex::BV>(
            left, right, std::move(sp));
    }

    // Bitwise

    /** Create an Expr with a Shift op
     *  Expr pointers may not be nullptr
     */
    template <Mode::Shift Mask>
    inline Expr::BasePtr shift(const Expr::BasePtr &left, const Expr::BasePtr &right,
                               Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Shift<Mask>, Private::SizeMode::First, Ex::BV>(
            left, right, std::move(sp));
    }

    /** Create an Expr with a Rotate op
     *  Expr pointers may not be nullptr
     */
    template <Mode::LR LR>
    inline Expr::BasePtr rotate(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Rotate<LR>, Private::SizeMode::First, Ex::BV>(
            left, right, std::move(sp));
    }

    // Misc

    /** Create an Expr with an Widen op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr widen(const Expr::BasePtr &left, const Expr::BasePtr &right,
                               Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Widen, Private::SizeMode::First, Ex::BV>(left, right,
                                                                                    std::move(sp));
    }

    /** Create an Expr with an Union op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr union_(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Union, Private::SizeMode::First, Ex::BV>(left, right,
                                                                                    std::move(sp));
    }

    /** Create an Expr with an Intersection op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    inline Expr::BasePtr intersection_(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                       Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<T, Op::Intersection, Private::first_or_na<T>, Ex::BV, Ex::Bool>(
            left, right, std::move(sp));
    }

    /** Create an Expr with an Concat op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    inline Expr::BasePtr concat(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<T, Op::Concat, Private::SizeMode::Add, Ex::BV, Ex::String>(
            left, right, std::move(sp));
    }

    /********************************************************************/
    /*                    Flat Passthrough Functions                    */
    /********************************************************************/

    // Math

    /** Create an Expr with an Add op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr add(Op::Add::OpContainer &&operands, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::flat<Ex::BV, Op::Add, Private::SizeMode::First, Ex::BV>(
            std::move(operands), std::move(sp));
    }

    /** Create an Expr with an Mul op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr mul(Op::Mul::OpContainer &&operands, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::flat<Ex::BV, Op::Mul, Private::SizeMode::First, Ex::BV>(
            std::move(operands), std::move(sp));
    }

    // Logical

    /** Create an Expr with an Or op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    inline Expr::BasePtr or_(Op::Or::OpContainer &&operands, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::flat<T, Op::Or, Private::first_or_na<T>, Ex::BV, Ex::Bool>(
            std::move(operands), std::move(sp));
    }

    /** Create an Expr with an And op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    inline Expr::BasePtr and_(Op::And::OpContainer &&operands, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::flat<T, Op::And, Private::first_or_na<T>, Ex::BV, Ex::Bool>(
            std::move(operands), std::move(sp));
    }

    /** Create an Expr with an Xor op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr xor_(Op::Xor::OpContainer &&operands, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::flat<Ex::BV, Op::Xor, Private::SizeMode::First, Ex::BV>(
            std::move(operands), std::move(sp));
    }

} // namespace Create


#endif
