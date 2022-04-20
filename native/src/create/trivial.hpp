/**
 * @file
 * @brief This file defines a group of create methods that are trivial passthrough methods
 * For example: Functions which just shell out to unary, binary, or flat
 */
#ifndef R_SRC_CREATE_TRIVIAL_HPP_
#define R_SRC_CREATE_TRIVIAL_HPP_

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
    inline Expr::BasePtr abs(const Expr::BasePtr &x, Annotation::SPAV sp = empty_spav) {
        return Private::unary<Op::Abs, Expr::FP>(x, std::move(sp));
    }

    /** Create an Expr with an Neg op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr neg(const Expr::BasePtr &x, Annotation::SPAV sp = empty_spav) {
        return Private::unary<Op::Neg, Expr::BV, Expr::FP>(x, std::move(sp));
    }

    /** Create an Expr with an Not op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr not_(const Expr::BasePtr &x, Annotation::SPAV sp = empty_spav) {
        return Private::unary<Op::Not, Expr::Bool>(x, std::move(sp));
    }

    /** Create an Expr with an Invert op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr invert(const Expr::BasePtr &x, Annotation::SPAV sp = empty_spav) {
        return Private::unary<Op::Invert, Expr::BV>(x, std::move(sp));
    }

    /** Create an Expr with an Reverse op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr reverse(const Expr::BasePtr &x, Annotation::SPAV sp = empty_spav) {
        return Private::unary<Op::Reverse, Expr::BV>(x, std::move(sp));
    }

    /********************************************************************/
    /*                UInt Binary Passthrough Functions                 */
    /********************************************************************/

    /** Create an Expr with an SignExt op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr sign_ext(const Expr::BasePtr &expr, const U64 integer,
                                  Annotation::SPAV sp = empty_spav) {
        return Private::uint_binary<U64, Op::SignExt, Private::SizeMode::Add, Expr::BV>(
            expr, integer, std::move(sp));
    }

    /** Create an Expr with an ZeroExt op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr zero_ext(const Expr::BasePtr &expr, const U64 integer,
                                  Annotation::SPAV sp = empty_spav) {
        return Private::uint_binary<U64, Op::ZeroExt, Private::SizeMode::Add, Expr::BV>(
            expr, integer, std::move(sp));
    }

    /********************************************************************/
    /*                   Binary Passthrough Functions                   */
    /********************************************************************/

    // Comparisons

    /** Create a Bool Expr with an Eq op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr eq(const Expr::BasePtr &left, const Expr::BasePtr &right,
                            Annotation::SPAV sp = empty_spav) {
        return Private::binary_explicit<Expr::Bool, Op::Eq, Private::SizeMode::NA, Expr::FP,
                                        Expr::Bool, Expr::BV, Expr::String>(left, right,
                                                                            std::move(sp));
    }

    /** Create a Bool Expr with an Neq op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr neq(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return Private::binary_explicit<Expr::Bool, Op::Neq, Private::SizeMode::NA, Expr::FP,
                                        Expr::Bool, Expr::BV, Expr::String>(left, right,
                                                                            std::move(sp));
    }

    /** Create an Expr with a Compare op
     *  Expr pointers may not be nullptr
     */
    template <Mode::Compare M>
    inline Expr::BasePtr compare(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                 Annotation::SPAV &&sp) {
        UTIL_ASSERT(Util::Err::Usage, Mode::is_signed(M) || !CUID::is_t<Expr::FP>(left),
                    "FP comparisons must be signed");
        return Private::binary_explicit<Expr::Bool, Op::Compare<M>, Private::SizeMode::NA, Expr::FP,
                                        Expr::BV>(left, right, std::move(sp));
    }

    /** A shortcut for compare<UGE>; exists for the API */
    inline Expr::BasePtr uge(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return compare<Mode::Compare::UGE>(left, right, std::move(sp));
    }

    /** A shortcut for compare<UGT>; exists for the API */
    inline Expr::BasePtr ugt(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return compare<Mode::Compare::UGT>(left, right, std::move(sp));
    }

    /** A shortcut for compare<ULE>; exists for the API */
    inline Expr::BasePtr ule(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return compare<Mode::Compare::ULE>(left, right, std::move(sp));
    }

    /** A shortcut for compare<ULT>; exists for the API */
    inline Expr::BasePtr ult(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return compare<Mode::Compare::ULT>(left, right, std::move(sp));
    }

    /** A shortcut for compare<SGE>; exists for the API */
    inline Expr::BasePtr sge(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return compare<Mode::Compare::SGE>(left, right, std::move(sp));
    }

    /** A shortcut for compare<SGT>; exists for the API */
    inline Expr::BasePtr sgt(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return compare<Mode::Compare::SGT>(left, right, std::move(sp));
    }

    /** A shortcut for compare<SLE>; exists for the API */
    inline Expr::BasePtr sle(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return compare<Mode::Compare::SLE>(left, right, std::move(sp));
    }

    /** A shortcut for compare<SLT>; exists for the API */
    inline Expr::BasePtr slt(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return compare<Mode::Compare::SLT>(left, right, std::move(sp));
    }

    // Math

    /** Create an Expr with an Sub op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr sub(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return Private::binary<Op::Sub, Private::SizeMode::First, Expr::BV>(left, right,
                                                                            std::move(sp));
    }

    /** Create an Expr with an Div op
     *  Expr pointers may not be nullptr
     */
    template <Mode::Signed Sgn>
    inline Expr::BasePtr div(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV &&sp) {
        return Private::binary<Op::Div<Sgn>, Private::SizeMode::First, Expr::BV>(left, right,
                                                                                 std::move(sp));
    }

    /** A shortcut for div<Signed>; exists for the API */
    inline Expr::BasePtr div_signed(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                    Annotation::SPAV sp = empty_spav) {
        return div<Mode::Signed::Signed>(left, right, std::move(sp));
    }

    /** A shortcut for div<Unsigned>; exists for the API */
    inline Expr::BasePtr div_unsigned(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                      Annotation::SPAV sp = empty_spav) {
        return div<Mode::Signed::Unsigned>(left, right, std::move(sp));
    }

    /** Create an Expr with an Mod op
     *  Expr pointers may not be nullptr
     */
    template <Mode::Signed Sgn>
    inline Expr::BasePtr mod(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV &&sp) {
        return Private::binary<Op::Mod<Sgn>, Private::SizeMode::First, Expr::BV>(left, right,
                                                                                 std::move(sp));
    }

    /** A shortcut for mod<Signed>; exists for the API */
    inline Expr::BasePtr mod_signed(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                    Annotation::SPAV sp = empty_spav) {
        return mod<Mode::Signed::Signed>(left, right, std::move(sp));
    }

    /** A shortcut for mod<Unsigned>; exists for the API */
    inline Expr::BasePtr mod_unsigned(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                      Annotation::SPAV sp = empty_spav) {
        return mod<Mode::Signed::Unsigned>(left, right, std::move(sp));
    }

    // Bitwise

    /** Create an Expr with a Shift op
     *  Expr pointers may not be nullptr
     */
    template <Mode::Shift Mask>
    inline Expr::BasePtr shift(const Expr::BasePtr &left, const Expr::BasePtr &right,
                               Annotation::SPAV &&sp) {
        return Private::binary<Op::Shift<Mask>, Private::SizeMode::First, Expr::BV>(left, right,
                                                                                    std::move(sp));
    }

    /** A shortcut for shift<Left>; exists for the API */
    inline Expr::BasePtr shift_l(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                 Annotation::SPAV sp = empty_spav) {
        return shift<Mode::Shift::Left>(left, right, std::move(sp));
    }

    /** A shortcut for shift<ArithmeticRight>; exists for the API */
    inline Expr::BasePtr shift_arithmetic_right(const Expr::BasePtr &left,
                                                const Expr::BasePtr &right,
                                                Annotation::SPAV sp = empty_spav) {
        return shift<Mode::Shift::ArithmeticRight>(left, right, std::move(sp));
    }

    /** A shortcut for shift<LogicalRight>; exists for the API */
    inline Expr::BasePtr shift_logical_right(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                             Annotation::SPAV sp = empty_spav) {
        return shift<Mode::Shift::LogicalRight>(left, right, std::move(sp));
    }

    /** Create an Expr with a Rotate op
     *  Expr pointers may not be nullptr
     */
    template <Mode::LR LR>
    inline Expr::BasePtr rotate(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                Annotation::SPAV &&sp) {
        return Private::binary<Op::Rotate<LR>, Private::SizeMode::First, Expr::BV>(left, right,
                                                                                   std::move(sp));
    }

    /** A shortcut for rotate<Left>; exists for the API */
    inline Expr::BasePtr rotate_left(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                     Annotation::SPAV sp = empty_spav) {
        return rotate<Mode::LR::Left>(left, right, std::move(sp));
    }

    /** A shortcut for rotate<Right>; exists for the API */
    inline Expr::BasePtr rotate_right(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                      Annotation::SPAV sp = empty_spav) {
        return rotate<Mode::LR::Right>(left, right, std::move(sp));
    }


    // Misc

    /** Create an Expr with an Widen op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr widen(const Expr::BasePtr &left, const Expr::BasePtr &right,
                               Annotation::SPAV sp = empty_spav) {
        return Private::binary<Op::Widen, Private::SizeMode::First, Expr::BV>(left, right,
                                                                              std::move(sp));
    }

    /** Create an Expr with an Union op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr union_(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                Annotation::SPAV sp = empty_spav) {
        return Private::binary<Op::Union, Private::SizeMode::First, Expr::BV>(left, right,
                                                                              std::move(sp));
    }

    /** Create an Expr with an Intersection op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr intersection_(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                       Annotation::SPAV sp = empty_spav) {
        return Private::binary<Op::Intersection, Private::SizeMode::First, Expr::BV, Expr::Bool>(
            left, right, std::move(sp));
    }

    /** Create an Expr with an Concat op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr concat(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                Annotation::SPAV sp = empty_spav) {
        return Private::binary<Op::Concat, Private::SizeMode::Add, Expr::BV, Expr::String>(
            left, right, std::move(sp));
    }

    /********************************************************************/
    /*                    Flat Passthrough Functions                    */
    /********************************************************************/

    // Math

    /** Create an Expr with an Add op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr add(Op::FlatArgs operands, Annotation::SPAV sp = empty_spav) {
        return Private::flat_explicit<Expr::BV, Op::Add, Expr::BV>(std::move(operands),
                                                                   std::move(sp));
    }

    /** Create an Expr with an Mul op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr mul(Op::FlatArgs operands, Annotation::SPAV sp = empty_spav) {
        return Private::flat_explicit<Expr::BV, Op::Mul, Expr::BV>(std::move(operands),
                                                                   std::move(sp));
    }

    // Logical

    /** Create an Expr with an Or op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr or_(Op::FlatArgs operands, Annotation::SPAV sp = empty_spav) {
        return Private::flat<Op::Or, Expr::BV, Expr::Bool>(std::move(operands), std::move(sp));
    }

    /** Create an Expr with an And op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr and_(Op::FlatArgs operands, Annotation::SPAV sp = empty_spav) {
        return Private::flat<Op::And, Expr::BV, Expr::Bool>(std::move(operands), std::move(sp));
    }

    /** Create an Expr with an Xor op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr xor_(Op::FlatArgs operands, Annotation::SPAV sp = empty_spav) {
        return Private::flat_explicit<Expr::BV, Op::Xor, Expr::BV>(std::move(operands),
                                                                   std::move(sp));
    }

} // namespace Create


#endif
