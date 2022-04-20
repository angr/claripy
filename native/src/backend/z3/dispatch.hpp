/**
 * @file
 * @brief This file defines the Z3 backend's dispatch functions
 */
#ifndef R_SRC_BACKEND_Z3_DISPATCH_HPP_
#define R_SRC_BACKEND_Z3_DISPATCH_HPP_

#include "abstract.hpp"
#include "constants.hpp"
#include "convert.hpp"


namespace Backend::Z3 {

    /** Used to dispatch conversions and abstractions between Claricpp exprs and Z3 ASTs */
    template <typename Z3> struct Dispatch final {
        static_assert(typename Z3::IsZ3Bk(), "Z3 should be the Z3 backend");

        /** This dynamic dispatcher converts expr into a backend object
         *  All arguments of expr that are not primitives have been
         *  pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         *  expr may not be nullptr
         *  Warning: This function may internally do unchecked static casting, we permit this
         *  *only* if the cuid of the expr is of or derive from the type being cast to.
         */
        static z3::expr dispatch_conversion(const Expr::RawPtr expr,
                                            std::vector<const z3::expr *> &args,
                                            SymAnTransData &satd, Z3 &bk) {
            UTIL_ASSERT_NOT_NULL_DEBUG(expr);
            UTIL_ASSERT_NOT_NULL_DEBUG(expr->op); // NOLINT Sanity check

            // We define local macros below to enforce consistency
            // across 'trivial' ops to reduce copy-paste errors.

#define UNARY_CASE(OP, FN)                                                                         \
    case Op::OP::static_cuid: {                                                                    \
        check_vec_usage(args, 1_ui);                                                               \
        auto ret { (FN) (*args.back()) };                                                          \
        args.pop_back();                                                                           \
        return ret;                                                                                \
    }

#define BINARY_DISPATCH(FN)                                                                        \
    check_vec_usage(args, 2_ui);                                                                   \
    const auto size { args.size() };                                                               \
    auto ret { (FN) (*args[size - 2], *args[size - 1]) };                                          \
    args.resize(size - 2);                                                                         \
    return ret;

#define BINARY_CASE(OP, FN)                                                                        \
    case Op::OP::static_cuid: {                                                                    \
        BINARY_DISPATCH((FN));                                                                     \
    }

// Passing templated objects to macros can be messy since ','s are in both
// For simplicity and consistency we define a binary op macro for this case
#define BINARY_TEMPLATE_CASE(OP, FN, ...)                                                          \
    case Op::OP<__VA_ARGS__>::static_cuid: {                                                       \
        const constexpr auto func { FN<__VA_ARGS__> };                                             \
        BINARY_DISPATCH(func);                                                                     \
    }

#define UINT_BINARY_CASE(OP, FN)                                                                   \
    case Op::OP::static_cuid: {                                                                    \
        static_assert(Op::is_uint_binary<Op::OP>, "Op::" #OP " is not UIntBinary");                \
        using To = CTSC<Op::UIntBinary>;                                                           \
        check_vec_usage(args, 1_ui);                                                               \
        auto ret { (FN) (*args.back(), Util::checked_static_cast<To>(expr->op.get())->integer) };  \
        args.pop_back();                                                                           \
        return ret;                                                                                \
    }

#define MODE_BINARY_CASE(OP, FN)                                                                   \
    case Op::OP::static_cuid: {                                                                    \
        static_assert(Op::FP::is_mode_binary<Op::OP>, "Op::" #OP " is not ModeBinary");            \
        using To = CTSC<Op::FP::ModeBinary>;                                                       \
        check_vec_usage(args, 2_ui);                                                               \
        const auto size { args.size() };                                                           \
        auto ret { (FN) (Util::checked_static_cast<To>(expr->op.get())->mode, *args[size - 2],     \
                         *args[size - 1]) };                                                       \
        args.resize(size - 2);                                                                     \
        return ret;                                                                                \
    }

#define TERNARY_CASE(OP, FN)                                                                       \
    case Op::OP::static_cuid: {                                                                    \
        const auto size { args.size() };                                                           \
        check_vec_usage(args, 3_ui);                                                               \
        auto ret { FN(*args[size - 3], *args[size - 2], *args[size - 1]) };                        \
        args.resize(size - 3);                                                                     \
        return ret;                                                                                \
    }

#define FLAT_CASE(OP, FN)                                                                          \
    case Op::OP::static_cuid: {                                                                    \
        static_assert(Op::is_flat<Op::OP>, "Op::" #OP " is not Flat");                             \
        using To = CTSC<Op::AbstractFlat>;                                                         \
        const auto a_size { args.size() };                                                         \
        const auto n { Util::checked_static_cast<To>(expr->op.get())->operands.size() };           \
        check_vec_usage(args, n);                                                                  \
        auto ret { (FN) (&(args.data()[a_size - n]), n) };                                         \
        args.resize(a_size - n);                                                                   \
        return ret;                                                                                \
    }

            // For brevity
            using Cmp = Mode::Compare;
            using Shift = Mode::Shift;
            using Sgn = Mode::Signed;

            // Switch on expr type
            switch (expr->op->cuid) {

                // This should never be hit
                default: {
                    UTIL_THROW(Util::Err::NotSupported,
                               "Unknown expr op given.\nOp CUID: ", expr->op->cuid);
                }

                    // Unsupported ops @todo
                case Op::Widen::static_cuid:           // fallthrough
                case Op::Union::static_cuid:           // fallthrough
                case Op::FP::FP::static_cuid:          // fallthrough
                case Op::String::IsDigit::static_cuid: // fallthrough
                case Op::Intersection::static_cuid: {
                    UTIL_THROW(Error::Backend::Unsupported,
                               "Unsupported expr op given.\nOp CUID: ", expr->op->cuid);
                }

                    /************************************************/
                    /*              Top-Level Trivial               */
                    /************************************************/

                    // Unary

                    UNARY_CASE(Neg, Conv::neg);
                    UNARY_CASE(Abs, Conv::abs);
                    UNARY_CASE(Not, Conv::not_);
                    UNARY_CASE(Invert, Conv::invert);
                    UNARY_CASE(Reverse, Conv::reverse);

                    // UIntBinary

                    UINT_BINARY_CASE(SignExt, Conv::signext);
                    UINT_BINARY_CASE(ZeroExt, Conv::zeroext);

                    // Binary

                    BINARY_CASE(Eq, Conv::eq);

                    BINARY_CASE(Neq, Conv::neq);

                    BINARY_TEMPLATE_CASE(Compare, Conv::template compare, Cmp::SGE);
                    BINARY_TEMPLATE_CASE(Compare, Conv::template compare, Cmp::SGT);
                    BINARY_TEMPLATE_CASE(Compare, Conv::template compare, Cmp::SLE);
                    BINARY_TEMPLATE_CASE(Compare, Conv::template compare, Cmp::SLT);
                    BINARY_TEMPLATE_CASE(Compare, Conv::template compare, Cmp::UGE);
                    BINARY_TEMPLATE_CASE(Compare, Conv::template compare, Cmp::UGT);
                    BINARY_TEMPLATE_CASE(Compare, Conv::template compare, Cmp::ULE);
                    BINARY_TEMPLATE_CASE(Compare, Conv::template compare, Cmp::ULT);

                    BINARY_CASE(Sub, Conv::sub);

                    BINARY_TEMPLATE_CASE(Div, Conv::template div, Sgn::Signed);
                    BINARY_TEMPLATE_CASE(Div, Conv::template div, Sgn::Unsigned);

                    BINARY_TEMPLATE_CASE(Mod, Conv::template mod, Sgn::Signed);
                    BINARY_TEMPLATE_CASE(Mod, Conv::template mod, Sgn::Unsigned);

                    BINARY_TEMPLATE_CASE(Shift, Conv::template shift, Shift::Left);
                    BINARY_TEMPLATE_CASE(Shift, Conv::template shift, Shift::ArithmeticRight);
                    BINARY_TEMPLATE_CASE(Shift, Conv::template shift, Shift::LogicalRight);

                    BINARY_TEMPLATE_CASE(Rotate, Conv::template rotate, Mode::LR::Left);
                    BINARY_TEMPLATE_CASE(Rotate, Conv::template rotate, Mode::LR::Right);

                    BINARY_CASE(Concat, Conv::concat);

                    // Flat

                    FLAT_CASE(Add, Conv::add);
                    FLAT_CASE(Mul, Conv::mul);
                    FLAT_CASE(Or, Conv::or_);
                    FLAT_CASE(And, Conv::and_);
                    FLAT_CASE(Xor, Conv::xor_);

                    // Other

                    TERNARY_CASE(If, Conv::if_);

                case Op::Extract::static_cuid: {
                    using To = CTSC<Op::Extract>;
                    check_vec_usage(args, 1);
                    const auto *const op { Util::checked_static_cast<To>(expr->op.get()) };
                    auto ret { Conv::extract(op->high, op->low, *args.back()) };
                    args.pop_back();
                    return ret;
                }
                case Op::Literal::static_cuid: {
                    return Conv::literal(expr, bk.tls.ctx);
                }
                case Op::Symbol::static_cuid: {
                    return Conv::symbol(expr, satd, bk.tls.ctx);
                }

                    /************************************************/
                    /*                  FP Trivial                  */
                    /************************************************/

                    // Unary

                    UNARY_CASE(FP::ToIEEEBV, Conv::FP::to_ieee_bv);

                    // Mode Binary

                    MODE_BINARY_CASE(FP::Add, Conv::FP::add);
                    MODE_BINARY_CASE(FP::Sub, Conv::FP::sub);
                    MODE_BINARY_CASE(FP::Mul, Conv::FP::mul);
                    MODE_BINARY_CASE(FP::Div, Conv::FP::div);

                    // Other

                    /** A local macro used for consistency */
#define TO_BV_CASE(TF)                                                                             \
    case Op::FP::ToBV<TF>::static_cuid: {                                                          \
        debug_assert_dcast<Expr::Bits>(expr, "FP::ToBV has no length");                            \
        using ToBV = CTSC<Op::FP::ToBV<TF>>;                                                       \
        check_vec_usage(args, 1);                                                                  \
        auto ret { Conv::FP::template to_bv<TF>(                                                   \
            Util::checked_static_cast<ToBV>(expr->op.get())->mode, *args.back(),                   \
            Expr::get_bit_length(expr)) };                                                         \
        args.pop_back();                                                                           \
        return ret;                                                                                \
    }

                    /** A local macro used for consistency */
#define FROM_2CBV_CASE(TF)                                                                         \
    case Op::FP::From2sComplementBV<TF>::static_cuid: {                                            \
        check_vec_usage(args, 1);                                                                  \
        using OpT = CTSC<Op::FP::From2sComplementBV<TF>>;                                          \
        const OpT cast_op { Util::checked_static_cast<OpT>(expr->op.get()) };                      \
        auto ret { Conv::FP::template from_2s_complement_bv<TF>(cast_op->mode, *args.back(),       \
                                                                cast_op->width) };                 \
        args.pop_back();                                                                           \
        return ret;                                                                                \
    }

                    // ToBV
                    TO_BV_CASE(Sgn::Signed);
                    TO_BV_CASE(Sgn::Unsigned);

                    // From2sComplementBV
                    FROM_2CBV_CASE(Sgn::Signed);
                    FROM_2CBV_CASE(Sgn::Unsigned);

                    // Cleanup
#undef TO_BV_CASE
#undef FROM_2CBV_CASE

                    // FromFP
                case Op::FP::FromFP::static_cuid: {
                    check_vec_usage(args, 1);
                    using FromFP = CTSC<Op::FP::FromFP>;
                    const FromFP cast_op { Util::checked_static_cast<FromFP>(expr->op.get()) };
                    auto ret { Conv::FP::from_fp(cast_op->mode, *args.back(), cast_op->width) };
                    args.pop_back();
                    return ret;
                }

                    // FromNot2sComplementBV
                case Op::FP::FromNot2sComplementBV::static_cuid: {
                    check_vec_usage(args, 1);
                    using OpT = CTSC<Op::FP::FromNot2sComplementBV>;
                    const OpT cast_op { Util::checked_static_cast<OpT>(expr->op.get()) };
                    auto ret { Conv::FP::from_not_2s_complement_bv(*args.back(), cast_op->width) };
                    args.pop_back();
                    return ret;
                }

                    /************************************************/
                    /*                String Trivial                */
                    /************************************************/

                    // Unary

                    UNARY_CASE(String::FromInt, Conv::String::from_int);

                    // Int Binary

                    UINT_BINARY_CASE(String::ToInt, Conv::String::to_int);
                    UINT_BINARY_CASE(String::Len, Conv::String::len);

                    // Binary

                    BINARY_CASE(String::Contains, Conv::String::contains);
                    BINARY_CASE(String::PrefixOf, Conv::String::prefix_of);
                    BINARY_CASE(String::SuffixOf, Conv::String::suffix_of);

                    // Ternary

                    TERNARY_CASE(String::Replace, Conv::String::replace);

                    // Other

                    TERNARY_CASE(String::SubString, Conv::String::substring);

                case Op::String::IndexOf::static_cuid: {
                    check_vec_usage(args, 2);
                    const auto size { args.size() };
                    debug_assert_dcast<Expr::Bits>(expr, "String::IndexOf has no length");
                    const auto bl { Expr::get_bit_length(expr) };
                    auto ret { Conv::String::index_of(*args[size - 3], *args[size - 2],
                                                      *args[size - 1], bl) };
                    args.resize(size - 2);
                    return ret;
                };
            }

// Cleanup
#undef UNARY_CASE
#undef BINARY_DISPATCH
#undef BINARY_CASE
#undef BINARY_TEMPLATE_CASE
#undef UINT_BINARY_CASE
#undef MODE_BINARY_CASE
#undef TERNARY_CASE
#undef FLAT_CASE
        }

        /** Abstract a backend object into a claricpp expr */
        static typename Z3::AbstractionVariant
        dispatch_abstraction(const z3::expr &b_obj,
                             std::vector<typename Z3::AbstractionVariant> &args,
                             SymAnTransData &satd) {

            // For brevity
            using C = Mode::Compare;
            using Shift = Mode::Shift;
            using Sign = Mode::Sign::FP;
            using Sgnd = Mode::Signed;

            // Get switching variables
            const auto decl { b_obj.decl() };
            const auto decl_kind { decl.decl_kind() };

            /** A local macro used for error checking */
#define ASSERT_ARG_EMPTY(X) UTIL_ASSERT(Util::Err::Size, (X).empty(), "Op should have no children");

            // Switch on expr type
            switch (decl_kind) {

                // Unknown op
                default: {
                    UTIL_THROW(Error::Backend::Abstraction,
                               "Unknown z3 op given. Op decl_kind: ", decl_kind,
                               "\nThe z3 op with this sort is:\n\t", b_obj);
                }

                    // Misc
                case Z3_OP_INTERNAL:
                    ASSERT_ARG_EMPTY(args);
                    return Abs::internal(b_obj, decl);
                case Z3_OP_UNINTERPRETED: {
                    return Abs::uninterpreted(b_obj, decl, args, satd);
                }

                    // Boolean
                case Z3_OP_TRUE:
                    ASSERT_ARG_EMPTY(args);
                    return Abs::template bool_<true>();
                case Z3_OP_FALSE:
                    ASSERT_ARG_EMPTY(args);
                    return Abs::template bool_<false>();

                    // Boolean logic
                case Z3_OP_EQ:
                    return Abs::eq(args);
                case Z3_OP_DISTINCT:
                    return Abs::distinct(args);
                case Z3_OP_ITE:
                    return Abs::ite(args);
                case Z3_OP_AND:
                    return Abs::and_(args);
                case Z3_OP_OR:
                    return Abs::or_(args);
                case Z3_OP_IFF:
                    return Abs::eq(args);
                case Z3_OP_XOR:
                    return Abs::xor_(args);
                case Z3_OP_NOT:
                    return Abs::template not_<Expr::Bool>(args);

                    // Comparisons
                case Z3_OP_ULEQ:
                    return Abs::template compare<C::ULE>(args);
                case Z3_OP_SLEQ:
                    return Abs::template compare<C::SLE>(args);
                case Z3_OP_UGEQ:
                    return Abs::template compare<C::UGE>(args);
                case Z3_OP_SGEQ:
                    return Abs::template compare<C::SGE>(args);
                case Z3_OP_ULT:
                    return Abs::template compare<C::ULT>(args);
                case Z3_OP_SLT:
                    return Abs::template compare<C::SLT>(args);
                case Z3_OP_UGT:
                    return Abs::template compare<C::UGT>(args);
                case Z3_OP_SGT:
                    return Abs::template compare<C::SGT>(args);

                    // Bit-vectors
                case Z3_OP_BNUM:
                    ASSERT_ARG_EMPTY(args);
                    return Abs::BV::num(b_obj);
                case Z3_OP_BNEG:
                    return Abs::neg(args);
                case Z3_OP_BADD:
                    return Abs::add(args);
                case Z3_OP_BSUB:
                    return Abs::sub(args);
                case Z3_OP_BMUL:
                    return Abs::mul(args);

                    // BV Arithmetic
                case Z3_OP_BSDIV: // fallthrough
                case Z3_OP_BSDIV_I:
                    return Abs::template div<Sgnd::Signed>(args);
                case Z3_OP_BUDIV: // fallthrough:
                case Z3_OP_BUDIV_I:
                    return Abs::template div<Sgnd::Unsigned>(args);
                case Z3_OP_BSMOD:   // fallthrough
                case Z3_OP_BSREM:   // fallthrough
                case Z3_OP_BSMOD_I: // fallthrough
                case Z3_OP_BSREM_I:
                    return Abs::template rem<Sgnd::Signed>(args);
                case Z3_OP_BUREM: // fallthrough
                case Z3_OP_BUREM_I:
                    return Abs::template rem<Sgnd::Unsigned>(args);

                    // BV Logic
                case Z3_OP_BAND:
                    return Abs::and_(args);
                case Z3_OP_BOR:
                    return Abs::or_(args);
                case Z3_OP_BNOT:
                    return Abs::template not_<Expr::BV>(args);
                case Z3_OP_BXOR:
                    return Abs::xor_(args);

                    // BV Bitwise Ops
                case Z3_OP_BSHL:
                    return Abs::template shift<Shift::Left>(args);
                case Z3_OP_BASHR:
                    return Abs::template shift<Shift::ArithmeticRight>(args);
                case Z3_OP_BLSHR:
                    return Abs::template shift<Shift::LogicalRight>(args);
                case Z3_OP_EXT_ROTATE_LEFT:
                    return Abs::template rotate<Mode::LR::Left>(args);
                case Z3_OP_EXT_ROTATE_RIGHT:
                    return Abs::template rotate<Mode::LR::Right>(args);

                    // BV Misc
                case Z3_OP_CONCAT:
                    return Abs::concat(args);
                case Z3_OP_SIGN_EXT:
                    return Abs::sign_ext(args, decl);
                case Z3_OP_ZERO_EXT:
                    return Abs::zero_ext(args, decl);
                case Z3_OP_EXTRACT:
                    return Abs::extract(args, b_obj);

                    // FP Conversions
                case Z3_OP_FPA_TO_SBV:
                    return Abs::FP::template to_bv<Sgnd::Signed>(args, decl);
                case Z3_OP_FPA_TO_UBV:
                    return Abs::FP::template to_bv<Sgnd::Unsigned>(args, decl);
                case Z3_OP_FPA_TO_IEEE_BV:
                    return Abs::FP::to_ieee_bv(args);
                case Z3_OP_FPA_TO_FP:
                    return Abs::FP::to_fp(args);
                case Z3_OP_FPA_NUM:
                    return Abs::FP::num(b_obj);

                    // FP Constants
                case Z3_OP_FPA_MINUS_ZERO:
                    ASSERT_ARG_EMPTY(args);
                    return Abs::FP::template zero<Sign::Minus>(b_obj);
                case Z3_OP_FPA_MINUS_INF:
                    ASSERT_ARG_EMPTY(args);
                    return Abs::FP::template inf<Sign::Minus>(b_obj);
                case Z3_OP_FPA_PLUS_ZERO:
                    ASSERT_ARG_EMPTY(args);
                    return Abs::FP::template zero<Sign::Plus>(b_obj);
                case Z3_OP_FPA_PLUS_INF:
                    ASSERT_ARG_EMPTY(args);
                    return Abs::FP::template inf<Sign::Plus>(b_obj);
                case Z3_OP_FPA_NAN:
                    ASSERT_ARG_EMPTY(args);
                    return Abs::FP::nan(b_obj);

                    // FP Comparisons
                case Z3_OP_FPA_EQ:
                    return Abs::eq(args);
                case Z3_OP_FPA_GT:
                    return Abs::template compare<C::SGT>(args);
                case Z3_OP_FPA_GE:
                    return Abs::template compare<C::SGE>(args);
                case Z3_OP_FPA_LT:
                    return Abs::template compare<C::SLT>(args);
                case Z3_OP_FPA_LE:
                    return Abs::template compare<C::SLE>(args);

                    // FP Arithmetic
                case Z3_OP_FPA_ABS:
                    return Abs::abs(args);
                case Z3_OP_FPA_NEG:
                    return Abs::neg(args);
                case Z3_OP_FPA_ADD:
                    return Abs::FP::add(args);
                case Z3_OP_FPA_SUB:
                    return Abs::FP::sub(args);
                case Z3_OP_FPA_MUL:
                    return Abs::FP::mul(args);
                case Z3_OP_FPA_DIV:
                    return Abs::FP::div(args);

                    // Rounding modes
                case Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN:
                    return Mode::FP::Rounding::NearestTiesEven;
                case Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY:
                    return Mode::FP::Rounding::NearestTiesAwayFromZero;
                case Z3_OP_FPA_RM_TOWARD_ZERO:
                    return Mode::FP::Rounding::TowardsZero;
                case Z3_OP_FPA_RM_TOWARD_POSITIVE:
                    return Mode::FP::Rounding::TowardsPositiveInf;
                case Z3_OP_FPA_RM_TOWARD_NEGATIVE:
                    return Mode::FP::Rounding::TowardsNegativeInf;
                    // Cleanup
#undef ASSERT_ARG_EMPTY
            }
        }

        /** Abstract a backend object into a primitive stored in a PrimVar */
        static Op::PrimVar dispatch_abstraction_to_prim(const z3::expr &b_obj) {
            UTIL_ASSERT(Util::Err::Size, b_obj.num_args() == 0, "Op should have no children");

            // Get switching variables
            const auto decl { b_obj.decl() };
            const auto decl_kind { decl.decl_kind() };

            // Switch on expr type
            switch (decl_kind) {
                default: {
                    UTIL_THROW(Error::Backend::Abstraction,
                               "Z3 backend cannot abstract given op to primitive; decl_kind: ",
                               decl_kind, "\nThe z3 op with this sort is:\n\t", b_obj);
                }

                // Boolean
                case Z3_OP_TRUE:
                    return true;
                case Z3_OP_FALSE:
                    return false;

                    // Conversions
                case Z3_OP_BNUM: {
                    const auto x { Abs::BV::num_primtive(b_obj) };
                    /** A local helper macro */
#define G_CASE(INDEX)                                                                              \
    case INDEX:                                                                                    \
        return std::get<INDEX>(x);
                    switch (x.index()) {
                        G_CASE(0)
                        G_CASE(1)
                        G_CASE(2)
                        G_CASE(3)
                        G_CASE(4)
                        default:
                            UTIL_THROW(Util::Err::Unknown, "Bad variant");
                    }
#undef G_CASE
                    static_assert(std::variant_size_v<decltype(x)> == 5,
                                  "Switch-case statement needs to be modified");
                }
                case Z3_OP_FPA_NUM: {
                    const std::variant<double, float> x { Abs::FP::num_primitive(b_obj) };
                    if (LIKELY(x.index() == 0)) {
                        return std::get<double>(x);
                    }
                    return std::get<float>(x);
                }

                    // FP Constants
                case Z3_OP_FPA_MINUS_ZERO: // fallthrough
                case Z3_OP_FPA_MINUS_INF:  // fallthrough
                case Z3_OP_FPA_PLUS_ZERO:  // fallthrough
                case Z3_OP_FPA_PLUS_INF:   // fallthrough
                case Z3_OP_FPA_NAN: {
                    const auto sort { b_obj.get_sort() };
                    const auto width { z3_sort_to_fp_width(sort) };
                    if (LIKELY(width == Mode::FP::dbl)) {
                        return fp_const<double>(decl_kind);
                    }
                    if (LIKELY(width == Mode::FP::flt)) {
                        return fp_const<float>(decl_kind);
                    }
                    UTIL_THROW(Util::Err::NotSupported, "Unsupported fp primitive width");
                }
                case Z3_OP_CONCAT: {
                    const auto sort { b_obj.get_sort() };
                    const auto width { z3_sort_to_fp_width(sort) };
                    if (LIKELY(width == Mode::FP::dbl)) {
                        return nan<double>;
                    }
                    if (LIKELY(width == Mode::FP::flt)) {
                        return nan<float>;
                    }
                    UTIL_THROW(Util::Err::NotSupported, "Unsupported fp primitive width");
                    // @todo: Fill in
#if 0
                    UTIL_ASSERT(Error::Backend::Abstraction, !Z3::rhfpu,
                            "rewriter.hi_fp_unspecified is set to false, this should not be triggered");
                        const auto n { b_obj.num_args() };
                        U64 res = 0; // @todo wrong
                        for (unsigned i { 0 }; i < n; ++i) {
                            auto arg { b_obj.arg(i) };
                            auto arg_decl { arg.decl() };
                            auto arg_kind { arg_decl.decl_kind() };
                            const auto arg_size { arg.get_sort().bv_size() };

                            bool neg { false };
                            if (arg_kind == Z3_OP_BNEG) {
                                arg = b_obj.arg(0);
                                arg_decl = arg.decl();
                                arg_kind = arg_decl.decl_kind();
                                neg = true;
                            }
                            if (arg_kind != Z3_OP_BNUM) {
                                UTIL_THROW(Error::Backend::Abstraction, "Weird z3 model");
                            }
                            auto arg_int { Abs::BV::num_primtive(arg) };
                            if (neg) {
                                arg_int = (1 << arg_size) - arg_int;
                            }
                            res <<= arg_size;
                            res |= arg_int;
                        }
                        return res;
#endif
                }
                case Z3_OP_FPA_TO_IEEE_BV: {
                    UTIL_ASSERT(
                        Error::Backend::Abstraction, rhfpu,
                        "rewriter.hi_fp_unspecified is set to true, this should not be triggered");
#ifdef DEBUG
                    UTIL_ASSERT(Util::Err::Size, b_obj.num_args() > 0,
                                "num_args should be at least one!");
#endif
                    const auto a0 { b_obj.arg(0) };
                    const auto var { Abs::FP::num_primitive(a0) };
                    static_assert(std::variant_size_v<decltype(var)> == 2, "Case needs updating");
                    switch (var.index()) {
                        case 0:
                            return std::get<0>(var);
                        case 1:
                            return std::get<1>(var);
                        default:
                            UTIL_THROW(Util::Err::Unknown, "Bad variant index");
                    }
                }

                    // String
                case Z3_OP_INTERNAL: {
                    UTIL_ASSERT(Error::Backend::Abstraction, string_check(b_obj),
                                "b_obj is not a string as expected");
                    return Abs::internal_primitive(b_obj, decl);
                }
            }
        }

      private:
        /** For brevity */
        using Conv = Convert<Z3>;
        /** For brevity */
        using Abs = Abstract<Z3>;

        /** A function that checks that *e is a subclass of T if DEBUG is enabled
         *  If not, a type exception prefixed by with message args... will be raised
         */
        template <typename T>
        static constexpr void debug_assert_dcast(const Expr::RawPtr e, CCSC msg) {
#ifdef DEBUG
            UTIL_ASSERT(Util::Err::Type, dynamic_cast<CTSC<T>>(e) != nullptr, msg);
#else
            (void) e;
            (void) msg;
#endif
        }

        /** Verify the container contains at least n elements
         *  In debug mode verifies that the last n elements are not nullptr
         */
        template <typename T> static void check_vec_usage(const T &c, const U64 n) {
            namespace Err = Util::Err; // NOLINT (false positive)
            UTIL_ASSERT(Err::Size, c.size() >= n, "container is too small to access ", n,
                        " elements");
#ifdef DEBUG
            if (n > 0) {
                const auto last { c.size() - 1 };
                for (U64 i { 0 }; i < n; ++i) {
                    UTIL_ASSERT(Err::Null, c[last - i] != nullptr,
                                "container element cannot be nullptr");
                }
            }
#endif
        }

        /** Return a T given the decl_kind */
        template <typename T> static T fp_const(const Z3_decl_kind &decl_kind) {
            static_assert(Util::Type::Is::in<T, float, double>, "Unsupported fp type");
            switch (decl_kind) {
                case Z3_OP_FPA_MINUS_ZERO:
                    return -0;
                case Z3_OP_FPA_MINUS_INF:
                    return -std::numeric_limits<T>::infinity(); // defined for float and double
                case Z3_OP_FPA_PLUS_ZERO:                       // fallthrough
                    return 0;
                case Z3_OP_FPA_PLUS_INF: // fallthrough
                    return std::numeric_limits<T>::infinity();
                case Z3_OP_FPA_NAN:
                    return nan<T>;
                default:
                    UTIL_THROW(Util::Err::Usage, "called with ba;d decl_kind: ", decl_kind);
            }
        }

        /** Return true if the expr is a z3 string */
        static bool string_check(const z3::expr &b_obj) {
            const auto sort { b_obj.get_sort() };
            if (sort.is_seq()) {
                return false;
            }
            // At this point we know b_obj encodes some kind of sequence
            const auto &ctx { b_obj.ctx() };
            const auto seq_basis_sort { Z3_get_seq_sort_basis(ctx, sort) };
            if (Z3_get_sort_kind(ctx, seq_basis_sort) != Z3_BV_SORT) {
                return false;
            }
            // At this point we know b_obj encodes a sequence of BVs
            // If each BV is 8 bit, b_obj encodes a sequence of 8-bit BVs
            // so we have a string! (per z3's definition of a string)
            return Z3_get_bv_sort_size(ctx, seq_basis_sort) == 8;
        }
    };

} // namespace Backend::Z3

#endif
