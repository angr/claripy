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
    inline EBasePtr abs(const EBasePtr &x, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::unary<Ex::FP, Ex::FP, Op::Abs, Ex::FP>(x, std::move(sp));
    }

    /** Create an Expr with an Neg op
     *  Expr pointers may not be nullptr
     */
    template <typename T> inline EBasePtr neg(const EBasePtr &x, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::unary<T, T, Op::Neg, Ex::BV, Ex::FP>(x, std::move(sp));
    }

    /** Create an Expr with an Not op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr not_(const EBasePtr &x, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::unary<Ex::Bool, Ex::Bool, Op::Not, Ex::Bool>(x, std::move(sp));
    }

    /** Create an Expr with an Invert op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr invert(const EBasePtr &x, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::unary<Ex::BV, Ex::BV, Op::Invert, Ex::BV>(x, std::move(sp));
    }

    /** Create an Expr with an Reverse op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr reverse(const EBasePtr &x, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::unary<Ex::BV, Ex::BV, Op::Reverse, Ex::BV>(x, std::move(sp));
    }

    /********************************************************************/
    /*                UInt Binary Passthrough Functions                 */
    /********************************************************************/

    /** Create an Expr with an SignExt op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr sign_ext(const EBasePtr &expr, const UInt integer,
                             Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::uint_binary<UInt, Ex::BV, Op::SignExt, Private::SizeMode::Add, Ex::BV>(
            expr, integer, std::move(sp));
    }

    /** Create an Expr with an ZeroExt op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr zero_ext(const EBasePtr &expr, const UInt integer,
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
    inline EBasePtr eq(const EBasePtr &left, const EBasePtr &right,
                       Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::Bool, T, Op::Eq, Private::SizeMode::NA, Ex::FP, Ex::Bool,
                               Ex::BV, Ex::String>(left, right, std::move(sp));
    }

    /** Create a Bool Expr with an Neq op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    inline EBasePtr neq(const EBasePtr &left, const EBasePtr &right,
                        Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::Bool, T, Op::Neq, Private::SizeMode::NA, Ex::FP, Ex::Bool,
                               Ex::BV, Ex::String>(left, right, std::move(sp));
    }

    /** Create an Expr with a Compare op
     *  Expr pointers may not be nullptr
     */
    template <typename In, Mode::Compare Mask>
    inline EBasePtr compare(const EBasePtr &left, const EBasePtr &right,
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
    inline EBasePtr sub(const EBasePtr &left, const EBasePtr &right,
                        Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Sub, Private::SizeMode::First, Ex::BV>(left, right,
                                                                                  std::move(sp));
    }

    /** Create an Expr with an Div op
     *  Expr pointers may not be nullptr
     */
    template <bool Signed>
    inline EBasePtr div(const EBasePtr &left, const EBasePtr &right,
                        Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Div<Signed>, Private::SizeMode::First, Ex::BV>(
            left, right, std::move(sp));
    }

    /** Create an Expr with an Mod op
     *  Expr pointers may not be nullptr
     */
    template <bool Signed>
    inline EBasePtr mod(const EBasePtr &left, const EBasePtr &right,
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
    inline EBasePtr shift(const EBasePtr &left, const EBasePtr &right,
                          Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Shift<Mask>, Private::SizeMode::First, Ex::BV>(
            left, right, std::move(sp));
    }

    /** Create an Expr with a Rotate op
     *  Expr pointers may not be nullptr
     */
    template <Mode::LR LR>
    inline EBasePtr rotate(const EBasePtr &left, const EBasePtr &right,
                           Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Rotate<LR>, Private::SizeMode::First, Ex::BV>(
            left, right, std::move(sp));
    }

    // Misc

    /** Create an Expr with an Widen op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr widen(const EBasePtr &left, const EBasePtr &right,
                          Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Widen, Private::SizeMode::First, Ex::BV>(left, right,
                                                                                    std::move(sp));
    }

    /** Create an Expr with an Union op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr union_(const EBasePtr &left, const EBasePtr &right,
                           Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<Ex::BV, Op::Union, Private::SizeMode::First, Ex::BV>(left, right,
                                                                                    std::move(sp));
    }

    /** Create an Expr with an Intersection op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    inline EBasePtr intersection_(const EBasePtr &left, const EBasePtr &right,
                                  Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::binary<T, Op::Intersection, Private::first_or_na<T>, Ex::BV, Ex::Bool>(
            left, right, std::move(sp));
    }

    /** Create an Expr with an Concat op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    inline EBasePtr concat(const EBasePtr &left, const EBasePtr &right,
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
    inline EBasePtr add(Op::Add::OpContainer &&operands, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::flat<Ex::BV, Op::Add, Private::SizeMode::First, Ex::BV>(
            std::move(operands), std::move(sp));
    }

    /** Create an Expr with an Mul op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr mul(Op::Mul::OpContainer &&operands, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::flat<Ex::BV, Op::Mul, Private::SizeMode::First, Ex::BV>(
            std::move(operands), std::move(sp));
    }

    // Logical

    /** Create an Expr with an Or op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    inline EBasePtr or_(Op::Or::OpContainer &&operands, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::flat<T, Op::Or, Private::first_or_na<T>, Ex::BV, Ex::Bool>(
            std::move(operands), std::move(sp));
    }

    /** Create an Expr with an And op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    inline EBasePtr and_(Op::And::OpContainer &&operands, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::flat<T, Op::And, Private::first_or_na<T>, Ex::BV, Ex::Bool>(
            std::move(operands), std::move(sp));
    }

    /** Create an Expr with an Xor op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr xor_(Op::Xor::OpContainer &&operands, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        return Private::flat<Ex::BV, Op::Xor, Private::SizeMode::First, Ex::BV>(
            std::move(operands), std::move(sp));
    }

} // namespace Create


#endif
