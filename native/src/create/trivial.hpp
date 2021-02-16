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

    /** Create a Expression with an Concat op */
    template <typename T>
    inline EBasePtr concat(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<T, Op::Concat, Private::SizeMode::Add, Ex::BV, Ex::String>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create a Bool Expression with an sub op */
    inline EBasePtr sub(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Sub, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create a Bool Expression with an div op */
    inline EBasePtr div(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::BV, Op::Div, Private::SizeMode::First, Ex::BV>(
            std::forward<EAnVec>(av), left, right);
    }

    /** Create a Bool Expression with an Eq op */
    template <typename T>
    inline EBasePtr eq(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<T, Op::Eq, Private::SizeMode::NA, Ex::FP, Ex::Bool, Ex::BV,
                               Ex::String>(std::forward<EAnVec>(av), left, right);
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
