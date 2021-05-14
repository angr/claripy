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

    /** Create an Expression with an Abs op */
    template <typename T> inline EBasePtr abs(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<T, T, Op::Abs, Ex::BV, Ex::FP>(std::forward<EAnVec>(av), x);
    }

    /** Create an Expression with an Neg op */
    template <typename T> inline EBasePtr neg(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<T, T, Op::Neg, Ex::BV, Ex::FP>(std::forward<EAnVec>(av), x);
    }

    /** Create an Expression with an Invert op */
    template <typename T> inline EBasePtr invert(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<T, T, Op::Invert, Ex::BV, Ex::Bool>(std::forward<EAnVec>(av), x);
    }

    /** Create an Expression with an Reverse op */
    inline EBasePtr reverse(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<Ex::BV, Ex::BV, Op::Reverse, Ex::BV>(std::forward<EAnVec>(av), x);
    }

    /********************************************************************/
    /*                 Int Binary Passthrough Functions                 */
    /********************************************************************/

    /** Create an Expression with an SignExt op */
    inline EBasePtr sign_ext(EAnVec &&av, const EBasePtr &expr, const Constants::UInt integer) {
        namespace Ex = Expression;
        return Private::uint_binary<Constants::UInt, Ex::BV, Op::SignExt, Private::SizeMode::Add,
                                    Ex::BV>(std::forward<EAnVec>(av), expr, integer);
    }

    /** Create an Expression with an ZeroExt op */
    inline EBasePtr zero_ext(EAnVec &&av, const EBasePtr &expr, const Constants::UInt integer) {
        namespace Ex = Expression;
        return Private::uint_binary<Constants::UInt, Ex::BV, Op::ZeroExt, Private::SizeMode::Add,
                                    Ex::BV>(std::forward<EAnVec>(av), expr, integer);
    }

    /********************************************************************/
    /*                   Binary Passthrough Functions                   */
    /********************************************************************/

    // Comparisons

    /** Create a Bool Expression with an Eq op */
    template <typename T>
    inline EBasePtr eq(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::Bool, T, Op::Eq, Private::SizeMode::NA, Ex::FP, Ex::Bool,
                               Ex::BV, Ex::String>(std::forward<EAnVec>(av), left, right);
    }

    /** Create a Bool Expression with an Neq op */
    template <typename T>
    inline EBasePtr neq(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::Bool, T, Op::Neq, Private::SizeMode::NA, Ex::FP, Ex::Bool,
                               Ex::BV, Ex::String>(std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with a Compare op */
    template <typename In, Mode::Compare Mask>
    inline EBasePtr compare(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        static_assert(Mode::compare_is_valid(Mask), "Invalid Compare Mode");
        if constexpr (Utils::is_same_ignore_const<In, Ex::FP>) {
            static_assert(Utils::BitMask::has(Mask, Mode::Compare::Signed),
                          "FP comparisons must be signed");
        }
        return Private::binary<Ex::Bool, In, Op::Compare<Mask>, Private::SizeMode::NA, Ex::FP,
                               Ex::BV>(std::forward<EAnVec>(av), left, right);
    }

    // Math

    /** Create an Expression with an Sub op */
    inline EBasePtr sub(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Sub, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an Div op */
    template <bool Signed>
    inline EBasePtr div(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Div<Signed>, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an Pow op */
    inline EBasePtr pow(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Pow, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an Mod op */
    template <bool Signed>
    inline EBasePtr mod(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Mod<Signed>, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    // Bitwise

    /** Create an Expression with a Shift op */
    template <Mode::Shift Mask>
    inline EBasePtr arithmetic_shift(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        static_assert(Mode::shift_is_valid(Mask), "Invalid Shift Mode");
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Shift<Mask>, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with a Rotate op */
    template <bool Left>
    inline EBasePtr rotate(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Rotate<Left>, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    // Misc

    /** Create an Expression with an Widen op */
    inline EBasePtr widen(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Widen, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an Union op */
    inline EBasePtr union_(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Union, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an Intersection op */
    template <typename T>
    inline EBasePtr intersection_(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<T, Op::Intersection, Private::first_or_na<T>, Ex::BV, Ex::Bool>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an Concat op */
    template <typename T>
    inline EBasePtr concat(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<T, Op::Concat, Private::SizeMode::Add, Ex::BV, Ex::String>(
            std::forward<EAnVec>(av), left, right);
    }

    /********************************************************************/
    /*                    Flat Passthrough Functions                    */
    /********************************************************************/

    // Math

    /** Create an Expression with an Add op */
    inline EBasePtr add(EAnVec &&av, Op::Add::OpContainer &&operands) {
        namespace Ex = Expression;
        return Private::flat<Ex::BV, Op::Add, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), std::forward<Op::Add::OpContainer>(operands));
    }

    /** Create an Expression with an Mul op */
    inline EBasePtr mul(EAnVec &&av, Op::Mul::OpContainer &&operands) {
        namespace Ex = Expression;
        return Private::flat<Ex::BV, Op::Mul, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), std::forward<Op::Mul::OpContainer>(operands));
    }

    // Logical

    /** Create an Expression with an Or op */
    template <typename T> inline EBasePtr or_(EAnVec &&av, Op::Or::OpContainer &&operands) {
        namespace Ex = Expression;
        return Private::flat<T, Op::Or, Private::first_or_na<T>, Ex::BV, Ex::Bool>(
            std::forward<EAnVec>(av), std::forward<Op::Or::OpContainer>(operands));
    }

    /** Create an Expression with an And op */
    template <typename T> inline EBasePtr and_(EAnVec &&av, Op::And::OpContainer &&operands) {
        namespace Ex = Expression;
        return Private::flat<T, Op::And, Private::first_or_na<T>, Ex::BV, Ex::Bool>(
            std::forward<EAnVec>(av), std::forward<Op::And::OpContainer>(operands));
    }

    /** Create an Expression with an Xor op */
    inline EBasePtr xor_(EAnVec &&av, Op::Xor::OpContainer &&operands) {
        namespace Ex = Expression;
        return Private::flat<Ex::BV, Op::Xor, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), std::forward<Op::Xor::OpContainer>(operands));
    }

} // namespace Create


#endif
