/**
 * @file
 * @brief This file defines a group of create methods that are trivial passthrough methods
 * For example: Functions which just shell out to unary, binary, or flat
 */
#ifndef __CREATE_TRIVIAL_HPP__
#define __CREATE_TRIVIAL_HPP__

#include "private/binary.hpp"
#include "private/flat.hpp"
#include "private/unary.hpp"


namespace Create {

    /********************************************************************/
    /*                   Unary Passthrough Functions                    */
    /********************************************************************/

    /** Create a Expression with an abs op */
    template <typename T> inline EBasePtr abs(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<T, Op::Abs, Ex::BV, Ex::FP>(std::forward<EAnVec>(av), x);
    }

    /** Create a Expression with an neg op */
    template <typename T> inline EBasePtr neg(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<T, Op::Neg, Ex::BV, Ex::FP>(std::forward<EAnVec>(av), x);
    }

    /** Create a Expression with an invert op */
    template <typename T> inline EBasePtr invert(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<T, Op::Invert, Ex::BV, Ex::Bool>(std::forward<EAnVec>(av), x);
    }

    /** Create a Expression with an reverse op */
    inline EBasePtr reverse(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<Ex::BV, Op::Reverse, Ex::BV>(std::forward<EAnVec>(av), x);
    }

    /********************************************************************/
    /*                   Binary Passthrough Functions                   */
    /********************************************************************/

    // Comparisons

    /** Create a Bool Expression with an Eq op */
    template <typename T>
    inline EBasePtr eq(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<T, Op::Eq, Private::SizeMode::NA, Ex::FP, Ex::Bool, Ex::BV,
                               Ex::String>(std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with a Compare op */
    template <typename In, bool Signed, bool Less, bool Eq>
    inline EBasePtr compare(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        if constexpr (Utils::is_same_ignore_const<In, Ex::FP>) {
            static_assert(Utils::TD::boolean<Signed, In>, "FP comparisons must be signed");
        }
        return Private::binary<Ex::Bool, In, Op::Compare<Signed, Less, Eq>, Private::SizeMode::NA,
                               Ex::FP, Ex::BV>(std::forward<EAnVec>(av), left, right);
    }

    // Math

    /** Create an Expression with an sub op */
    inline EBasePtr sub(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Sub, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an div op */
    inline EBasePtr div(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Div, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an Or op */
    inline EBasePtr pow(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Pow, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an Or op */
    inline EBasePtr mod(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Mod, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an Or op */
    inline EBasePtr div_mod(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::DivMod, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    // Bitwise

    /** Create an Expression with a Shift op */
    template <bool Left>
    inline EBasePtr shift(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Shift<Left>, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with a Rotate op */
    template <bool Left>
    inline EBasePtr rotate(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Rotate<Left>, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    // Logical

    /** Create an Expression with an Or op */
    template <typename T>
    inline EBasePtr or_(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<T, Op::Or, Private::first_or_na<T>, Ex::BV, Ex::Bool>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an And op */
    template <typename T>
    inline EBasePtr and_(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<T, Op::And, Private::first_or_na<T>, Ex::BV, Ex::Bool>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with an Xor op */
    inline EBasePtr xor_(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Xor, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    // Misc

    /** Create a Expression with an Concat op */
    template <typename T>
    inline EBasePtr concat(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<T, Op::Concat, Private::SizeMode::Add, Ex::BV, Ex::String>(
            std::forward<EAnVec>(av), left, right);
    }

    /********************************************************************/
    /*                    Flat Passthrough Functions                    */
    /********************************************************************/

    /** Create a Expression with an Add op */
    inline EBasePtr add(EAnVec &&av, Op::Add::OpContainer &&operands) {
        namespace Ex = Expression;
        return Private::flat<Ex::BV, Op::Add, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), std::forward<Op::Add::OpContainer>(operands));
    }

    /** Create a Expression with an Mul op */
    inline EBasePtr mul(EAnVec &&av, Op::Mul::OpContainer &&operands) {
        namespace Ex = Expression;
        return Private::flat<Ex::BV, Op::Mul, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), std::forward<Op::Mul::OpContainer>(operands));
    }

} // namespace Create


#endif
