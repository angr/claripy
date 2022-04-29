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

    /** Create an Expr with an Inequality op
     *  Expr pointers may not be nullptr
     */
    template <typename OpT>
    inline Expr::BasePtr inequality(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                    Annotation::SPAV &&sp) {
        static_assert(std::is_base_of_v<Op::Inequality, OpT>, "Op must derive from inequality");
        if constexpr (Util::Type::Is::in<OpT, Op::UGE, Op::UGT, Op::ULE, Op::ULT>) {
            UTIL_ASSERT(Util::Err::Usage, not CUID::is_t<Expr::FP>(left),
                        "FP comparisons must be signed");
        }
        return Private::binary_explicit<Expr::Bool, OpT, Private::SizeMode::NA, Expr::FP, Expr::BV>(
            left, right, std::move(sp));
    }

    /** A shortcut for inequality<UGE>; exists for the API */
    inline Expr::BasePtr uge(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return inequality<Op::UGE>(left, right, std::move(sp));
    }

    /** A shortcut for inequality<UGT>; exists for the API */
    inline Expr::BasePtr ugt(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return inequality<Op::UGT>(left, right, std::move(sp));
    }

    /** A shortcut for inequality<ULE>; exists for the API */
    inline Expr::BasePtr ule(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return inequality<Op::ULE>(left, right, std::move(sp));
    }

    /** A shortcut for inequality<ULT>; exists for the API */
    inline Expr::BasePtr ult(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return inequality<Op::ULT>(left, right, std::move(sp));
    }

    /** A shortcut for inequality<SGE>; exists for the API */
    inline Expr::BasePtr sge(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return inequality<Op::SGE>(left, right, std::move(sp));
    }

    /** A shortcut for inequality<SGT>; exists for the API */
    inline Expr::BasePtr sgt(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return inequality<Op::SGT>(left, right, std::move(sp));
    }

    /** A shortcut for inequality<SLE>; exists for the API */
    inline Expr::BasePtr sle(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return inequality<Op::SLE>(left, right, std::move(sp));
    }

    /** A shortcut for inequality<SLT>; exists for the API */
    inline Expr::BasePtr slt(const Expr::BasePtr &left, const Expr::BasePtr &right,
                             Annotation::SPAV sp = empty_spav) {
        return inequality<Op::SLT>(left, right, std::move(sp));
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

    /** Create an Expr with a DivSigned op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr div_signed(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                    Annotation::SPAV sp = empty_spav) {
        return Private::binary<Op::DivSigned, Private::SizeMode::First, Expr::BV>(left, right,
                                                                                  std::move(sp));
    }

    /** Create an Expr with a DivUnsigned op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr div_unsigned(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                      Annotation::SPAV sp = empty_spav) {
        return Private::binary<Op::DivUnsigned, Private::SizeMode::First, Expr::BV>(left, right,
                                                                                    std::move(sp));
    }

    /** Create an Expr with an Mod op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr mod_signed(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                    Annotation::SPAV sp = empty_spav) {
        return Private::binary<Op::ModSigned, Private::SizeMode::First, Expr::BV>(left, right,
                                                                                  std::move(sp));
    }

    /** Create an Expr with an Mod op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr mod_unsigned(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                      Annotation::SPAV sp = empty_spav) {
        return Private::binary<Op::ModUnsigned, Private::SizeMode::First, Expr::BV>(left, right,
                                                                                    std::move(sp));
    }

    // Bitwise

    /** Create an Expr with a Shift op
     *  Expr pointers may not be nullptr
     */
    template <typename OpT>
    inline Expr::BasePtr shift(const Expr::BasePtr &left, const Expr::BasePtr &right,
                               Annotation::SPAV &&sp) {
        static_assert(std::is_base_of_v<Op::Shift, OpT>, "OpT must be a Shift op");
        return Private::binary<OpT, Private::SizeMode::First, Expr::BV>(left, right, std::move(sp));
    }

    /** A shortcut for shift<ShiftLeft>; exists for the API */
    inline Expr::BasePtr shift_l(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                 Annotation::SPAV sp = empty_spav) {
        return shift<Op::ShiftLeft>(left, right, std::move(sp));
    }

    /** A shortcut for shift<ShiftArithmeticRight>; exists for the API */
    inline Expr::BasePtr shift_arithmetic_right(const Expr::BasePtr &left,
                                                const Expr::BasePtr &right,
                                                Annotation::SPAV sp = empty_spav) {
        return shift<Op::ShiftArithmeticRight>(left, right, std::move(sp));
    }

    /** A shortcut for shift<ShiftLogicalRight>; exists for the API */
    inline Expr::BasePtr shift_logical_right(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                             Annotation::SPAV sp = empty_spav) {
        return shift<Op::ShiftLogicalRight>(left, right, std::move(sp));
    }

    /** Create an Expr with a RotateLeft op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr rotate_left(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                     Annotation::SPAV sp = empty_spav) {
        return Private::binary<Op::RotateLeft, Private::SizeMode::First, Expr::BV>(left, right,
                                                                                   std::move(sp));
    }

    /** Create an Expr with a RotateRight op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr rotate_right(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                      Annotation::SPAV sp = empty_spav) {
        return Private::binary<Op::RotateRight, Private::SizeMode::First, Expr::BV>(left, right,
                                                                                    std::move(sp));
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
