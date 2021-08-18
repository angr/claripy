/**
 * @file
 * @brief This file defines the Z3 backend's dispatch functions
 */
#ifndef R_BACKEND_Z3_DISPATCH_HPP_
#define R_BACKEND_Z3_DISPATCH_HPP_

#include "abstract.hpp"
#include "constants.hpp"
#include "convert.hpp"


namespace Backend::Z3::Private {

    /** The Z3 Abstraction variant */
    using AbstractionVariant = Z3Super::AbstractionVariant;

    /** The symbol_annotation_translocation_data type */
    using SATD = std::map<std::string, Expression::Base::SPAV>;

    /** Verify the container contains at least n elements
     *  In debug mode verifies that the last n elements are not nullptr
     */
    template <typename T, typename... Args>
    inline void check_vec_usage(const T &c, const Constants::UInt n, Args &&...args) {
        namespace Err = Utils::Error::Unexpected; // NOLINT (false positive)
        Utils::affirm<Err::Size>(c.size() >= n, std::forward<Args>(args)...,
                                 "container is too small to access ", n, " elements");
#ifdef DEBUG
        if (n > 0) {
            const auto last { c.size() - 1 };
            for (Constants::UInt i { 0 }; i < n; ++i) {
                Utils::affirm<Err::Null>(c[last - i] != nullptr, std::forward<Args>(args)...,
                                         "container element cannot be nullptr");
            }
        }
#endif
    }

    /** A function that checks that *e is a subclass of T if DEBUG is enabled
     *  If not, a type exception prefixed by with message args... will be raised
     */
    template <typename T, typename... Args>
    static constexpr void debug_assert_dcast(const Expression::RawPtr e, Args &&...args) {
#ifdef DEBUG
        using Ptr = Constants::CTSC<T>;
        using Err = Utils::Error::Unexpected::Type;
        Utils::affirm<Err>(dynamic_cast<Ptr>(e) != nullptr, std::forward<Args>(args)...);
#else
        Utils::sink(e, args...);
#endif
    }

    /** This dynamic dispatcher converts expr into a backend object
     *  All arguments of expr that are not primitives have been
     *  pre-converted into backend objects and are in args
     *  Arguments must be popped off the args stack if used
     *  expr may not be nullptr
     *  Warning: This function may internally do unchecked static casting, we permit this
     *  *only* if the cuid of the expression is of or derive from the type being cast to.
     */
    inline z3::expr dispatch_conversion(const Expression::RawPtr expr,
                                        std::vector<const z3::expr *> &args, SATD &satd) {
        UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
        UTILS_AFFIRM_NOT_NULL_DEBUG(expr->op); // NOLINT Sanity check

        // We define local macros below to enforce consistency
        // across 'trivial' ops to reduce copy-paste errors.

#define UNARY_CASE(OP, FN)                                                                        \
    case Op::OP::static_cuid: {                                                                   \
        check_vec_usage(args, 1_ui, WHOAMI_WITH_SOURCE);                                          \
        auto ret { (FN) (*args.back()) };                                                         \
        args.pop_back();                                                                          \
        return ret;                                                                               \
    }

#define BINARY_DISPATCH(FN)                                                                       \
    check_vec_usage(args, 2_ui, WHOAMI_WITH_SOURCE);                                              \
    const auto size { args.size() };                                                              \
    auto ret { (FN) (*args[size - 2], *args[size - 1]) };                                         \
    args.resize(size - 2);                                                                        \
    return ret;

#define BINARY_CASE(OP, FN)                                                                       \
    case Op::OP::static_cuid: {                                                                   \
        BINARY_DISPATCH((FN));                                                                    \
    }

// Passing templated objects to macros can be messy since ','s are in both
// For simplicity and consistency we define a binary op macro for this case
#define BINARY_TEMPLATE_CASE(OP, FN, ...)                                                         \
    case Op::OP<__VA_ARGS__>::static_cuid: {                                                      \
        const constexpr auto func { FN<__VA_ARGS__> };                                            \
        BINARY_DISPATCH(func);                                                                    \
    }

#define UINT_BINARY_CASE(OP, FN)                                                                  \
    case Op::OP::static_cuid: {                                                                   \
        static_assert(Op::is_uint_binary<Op::OP>, "Op::" #OP " is not UIntBinary");               \
        using To = Constants::CTSC<Op::UIntBinary>;                                               \
        check_vec_usage(args, 1_ui, WHOAMI_WITH_SOURCE);                                          \
        auto ret { (FN) (*args.back(),                                                            \
                         Utils::checked_static_cast<To>(expr->op.get())->integer) };              \
        args.pop_back();                                                                          \
        return ret;                                                                               \
    }

#define MODE_BINARY_CASE(OP, FN)                                                                  \
    case Op::OP::static_cuid: {                                                                   \
        static_assert(Op::FP::is_mode_binary<Op::OP>, "Op::" #OP " is not ModeBinary");           \
        using To = Constants::CTSC<Op::FP::ModeBinary>;                                           \
        check_vec_usage(args, 2_ui, WHOAMI_WITH_SOURCE);                                          \
        const auto size { args.size() };                                                          \
        auto ret { (FN) (Utils::checked_static_cast<To>(expr->op.get())->mode, *args[size - 2],   \
                         *args[size - 1]) };                                                      \
        args.resize(size - 2);                                                                    \
        return ret;                                                                               \
    }

#define TERNARY_CASE(OP, FN)                                                                      \
    case Op::OP::static_cuid: {                                                                   \
        const auto size { args.size() };                                                          \
        check_vec_usage(args, 3_ui, WHOAMI_WITH_SOURCE);                                          \
        auto ret { FN(*args[size - 3], *args[size - 2], *args[size - 1]) };                       \
        args.resize(size - 3);                                                                    \
        return ret;                                                                               \
    }

#define FLAT_CASE(OP, FN)                                                                         \
    case Op::OP::static_cuid: {                                                                   \
        static_assert(Op::is_flat<Op::OP>, "Op::" #OP " is not Flat");                            \
        using To = Constants::CTSC<Op::AbstractFlat>;                                             \
        const auto a_size { args.size() };                                                        \
        const auto n { Utils::checked_static_cast<To>(expr->op.get())->operands.size() };         \
        check_vec_usage(args, n, WHOAMI_WITH_SOURCE);                                             \
        auto ret { (FN) (&(args.data()[a_size - n]), n) };                                        \
        args.resize(a_size - n);                                                                  \
        return ret;                                                                               \
    }

        // For brevity
        using Cmp = Mode::Compare;
        using Shift = Mode::Shift;

        // Switch on expr type
        switch (expr->op->cuid) {

            // This should never be hit
            default: {
                throw Utils::Error::Unexpected::NotSupported(
                    WHOAMI_WITH_SOURCE "Unknown expression op given.\nOp CUID: ", expr->op->cuid);
            }

                // Unsupported ops
            case Op::Widen::static_cuid:           // fallthrough
            case Op::Union::static_cuid:           // fallthrough
            case Op::FP::FP::static_cuid:          // fallthrough
            case Op::String::IsDigit::static_cuid: // fallthrough
            case Op::Intersection::static_cuid: {
                throw Error::Backend::Unsupported(WHOAMI_WITH_SOURCE
                                                  "Unsupported expression op given.\nOp CUID: ",
                                                  expr->op->cuid);
            }

                /************************************************/
                /*              Top-Level Trivial               */
                /************************************************/

                // Unary

                UNARY_CASE(Neg, Convert::neg);
                UNARY_CASE(Abs, Convert::abs);
                UNARY_CASE(Not, Convert::not_);
                UNARY_CASE(Invert, Convert::invert);
                UNARY_CASE(Reverse, Convert::reverse);

                // UIntBinary

                UINT_BINARY_CASE(SignExt, Convert::signext);
                UINT_BINARY_CASE(ZeroExt, Convert::zeroext);

                // Binary

                BINARY_CASE(Eq, Convert::eq);

                BINARY_CASE(Neq, Convert::neq);

                BINARY_TEMPLATE_CASE(Compare, Convert::compare,
                                     Cmp::Signed | Cmp::Greater | Cmp::Eq);
                BINARY_TEMPLATE_CASE(Compare, Convert::compare,
                                     Cmp::Signed | Cmp::Greater | Cmp::Neq);
                BINARY_TEMPLATE_CASE(Compare, Convert::compare, Cmp::Signed | Cmp::Less | Cmp::Eq);
                BINARY_TEMPLATE_CASE(Compare, Convert::compare,
                                     Cmp::Signed | Cmp::Less | Cmp::Neq);
                BINARY_TEMPLATE_CASE(Compare, Convert::compare,
                                     Cmp::Unsigned | Cmp::Greater | Cmp::Eq);
                BINARY_TEMPLATE_CASE(Compare, Convert::compare,
                                     Cmp::Unsigned | Cmp::Greater | Cmp::Neq);
                BINARY_TEMPLATE_CASE(Compare, Convert::compare,
                                     Cmp::Unsigned | Cmp::Less | Cmp::Eq);
                BINARY_TEMPLATE_CASE(Compare, Convert::compare,
                                     Cmp::Unsigned | Cmp::Less | Cmp::Neq);

                BINARY_CASE(Sub, Convert::sub);

                BINARY_TEMPLATE_CASE(Div, Convert::div, true);
                BINARY_TEMPLATE_CASE(Div, Convert::div, false);

                BINARY_TEMPLATE_CASE(Mod, Convert::mod, true);
                BINARY_TEMPLATE_CASE(Mod, Convert::mod, false);

                BINARY_TEMPLATE_CASE(Shift, Convert::shift, Shift::Left);
                BINARY_TEMPLATE_CASE(Shift, Convert::shift, Shift::ArithmeticRight);
                BINARY_TEMPLATE_CASE(Shift, Convert::shift, Shift::LogicalRight);

                BINARY_TEMPLATE_CASE(Rotate, Convert::rotate, Mode::LR::Left);
                BINARY_TEMPLATE_CASE(Rotate, Convert::rotate, Mode::LR::Right);

                BINARY_CASE(Concat, Convert::concat);

                // Flat

                FLAT_CASE(Add, Convert::add);
                FLAT_CASE(Mul, Convert::mul);
                FLAT_CASE(Or, Convert::or_);
                FLAT_CASE(And, Convert::and_);
                FLAT_CASE(Xor, Convert::xor_);

                // Other

                TERNARY_CASE(If, Convert::if_);

            case Op::Extract::static_cuid: {
                using To = Constants::CTSC<Op::Extract>;
                check_vec_usage(args, 1, WHOAMI_WITH_SOURCE);
                const auto *const op { Utils::checked_static_cast<To>(expr->op.get()) };
                auto ret { Convert::extract(op->high, op->low, *args.back()) };
                args.pop_back();
                return ret;
            }
            case Op::Literal::static_cuid: {
                return Convert::literal(expr);
            }
            case Op::Symbol::static_cuid: {
                return Convert::symbol(expr, satd);
            }

                /************************************************/
                /*                  FP Trivial                  */
                /************************************************/

                // Unary

                UNARY_CASE(FP::ToIEEEBV, Convert::FP::to_ieee_bv);

                // Mode Binary

                MODE_BINARY_CASE(FP::Add, Convert::FP::add);
                MODE_BINARY_CASE(FP::Sub, Convert::FP::sub);
                MODE_BINARY_CASE(FP::Mul, Convert::FP::mul);
                MODE_BINARY_CASE(FP::Div, Convert::FP::div);

                // Other

                /** A local macro used for consistency */
#define TO_BV_CASE(TF)                                                                            \
    case Op::FP::ToBV<TF>::static_cuid: {                                                         \
        debug_assert_dcast<Expression::Bits>(expr, WHOAMI_WITH_SOURCE "FP::ToBV has no length");  \
        using ToBV = Constants::CTSC<Op::FP::ToBV<TF>>;                                           \
        check_vec_usage(args, 1, WHOAMI_WITH_SOURCE);                                             \
        auto ret { Convert::FP::to_bv<TF>(Utils::checked_static_cast<ToBV>(expr->op.get())->mode, \
                                          *args.back(), Expression::get_bit_length(expr)) };      \
        args.pop_back();                                                                          \
        return ret;                                                                               \
    }

                /** A local macro used for consistency */
#define FROM_2CBV_CASE(TF)                                                                        \
    case Op::FP::From2sComplementBV<TF>::static_cuid: {                                           \
        check_vec_usage(args, 1, WHOAMI_WITH_SOURCE);                                             \
        using OpT = Constants::CTSC<Op::FP::From2sComplementBV<TF>>;                              \
        const OpT cast_op { Utils::checked_static_cast<OpT>(expr->op.get()) };                    \
        auto ret { Convert::FP::from_2s_complement_bv<TF>(cast_op->mode, *args.back(),            \
                                                          cast_op->width) };                      \
        args.pop_back();                                                                          \
        return ret;                                                                               \
    }

                // ToBV
                TO_BV_CASE(true);
                TO_BV_CASE(false);

                // From2sComplementBV
                FROM_2CBV_CASE(true);
                FROM_2CBV_CASE(false);

                // Cleanup
#undef TO_BV_CASE
#undef FROM_2CBV_CASE

                // FromFP
            case Op::FP::FromFP::static_cuid: {
                check_vec_usage(args, 1, WHOAMI_WITH_SOURCE);
                using FromFP = Constants::CTSC<Op::FP::FromFP>;
                const FromFP cast_op { Utils::checked_static_cast<FromFP>(expr->op.get()) };
                auto ret { Convert::FP::from_fp(cast_op->mode, *args.back(), cast_op->width) };
                args.pop_back();
                return ret;
            }

                // FromNot2sComplementBV
            case Op::FP::FromNot2sComplementBV::static_cuid: {
                check_vec_usage(args, 1, WHOAMI_WITH_SOURCE);
                using OpT = Constants::CTSC<Op::FP::FromNot2sComplementBV>;
                const OpT cast_op { Utils::checked_static_cast<OpT>(expr->op.get()) };
                auto ret { Convert::FP::from_not_2s_complement_bv(*args.back(), cast_op->width) };
                args.pop_back();
                return ret;
            }

                /************************************************/
                /*                String Trivial                */
                /************************************************/

                // Unary

                UNARY_CASE(String::FromInt, Convert::String::from_int);

                // Int Binary

                UINT_BINARY_CASE(String::ToInt, Convert::String::to_int);
                UINT_BINARY_CASE(String::Len, Convert::String::len);

                // Binary

                BINARY_CASE(String::Contains, Convert::String::contains);
                BINARY_CASE(String::PrefixOf, Convert::String::prefix_of);
                BINARY_CASE(String::SuffixOf, Convert::String::suffix_of);

                // Ternary

                TERNARY_CASE(String::Replace, Convert::String::replace);

                // Other

                TERNARY_CASE(String::SubString, Convert::String::substring);

            case Op::String::IndexOf::static_cuid: {
                check_vec_usage(args, 2, WHOAMI_WITH_SOURCE);
                const auto size { args.size() };
                debug_assert_dcast<Expression::Bits>(expr, WHOAMI_WITH_SOURCE
                                                     "String::IndexOf has no length");
                const auto bl { Expression::get_bit_length(expr) };
                auto ret { Convert::String::index_of(*args[size - 3], *args[size - 2],
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

    /** Abstract a backend object into a claricpp expression */
    inline AbstractionVariant dispatch_abstraction(const z3::expr &b_obj,
                                                   std::vector<AbstractionVariant> &args,
                                                   SATD &satd) {

        // For brevity
        using C = Mode::Compare;
        using Shift = Mode::Shift;
        using Sign = Mode::Sign::FP;
        namespace Ex = Expression;

        // Get switching variables
        const auto decl { b_obj.decl() };
        const auto decl_kind { decl.decl_kind() };

        /** A local macro used for error checking */
#define ASSERT_ARG_EMPTY(X)                                                                       \
    Utils::affirm<Utils::Error::Unexpected::Size>((X).empty(), WHOAMI_WITH_SOURCE                 \
                                                  "Op should have no children");

        // Switch on expr type
        switch (decl_kind) {

            // Unknown op
            default: {
                throw Error::Backend::Abstraction(
                    WHOAMI_WITH_SOURCE "Unknown z3 op given. Op decl_kind: ", decl_kind,
                    "\nThe z3 op with this sort is:\n\t", b_obj);
            }

                // Misc
            case Z3_OP_INTERNAL:
                ASSERT_ARG_EMPTY(args);
                return Abstract::internal(b_obj, decl);
            case Z3_OP_UNINTERPRETED: {
                return Abstract::uninterpreted(b_obj, decl, args, satd);
            }

                // Boolean
            case Z3_OP_TRUE:
                ASSERT_ARG_EMPTY(args);
                return Abstract::bool_<true>;
            case Z3_OP_FALSE:
                ASSERT_ARG_EMPTY(args);
                return Abstract::bool_<false>;

                // Boolean logic
            case Z3_OP_EQ:
                return Abstract::eq(args);
            case Z3_OP_DISTINCT:
                return Abstract::distinct(args);
            case Z3_OP_ITE:
                return Abstract::ite(args);
            case Z3_OP_AND:
                return Abstract::and_<Ex::Bool>(args);
            case Z3_OP_OR:
                return Abstract::or_<Ex::Bool>(args);
            case Z3_OP_IFF:
                return Abstract::eq<Ex::Bool>(args);
            case Z3_OP_XOR:
                return Abstract::xor_<Ex::Bool>(args);
            case Z3_OP_NOT:
                return Abstract::not_<Ex::Bool>(args);

                // Comparisons
            case Z3_OP_ULEQ:
                return Abstract::compare<Ex::BV, C::Unsigned | C::Less | C::Eq>(args);
            case Z3_OP_SLEQ:
                return Abstract::compare<Ex::BV, C::Signed | C::Less | C::Eq>(args);
            case Z3_OP_UGEQ:
                return Abstract::compare<Ex::BV, C::Unsigned | C::Greater | C::Eq>(args);
            case Z3_OP_SGEQ:
                return Abstract::compare<Ex::BV, C::Signed | C::Greater | C::Eq>(args);
            case Z3_OP_ULT:
                return Abstract::compare<Ex::BV, C::Unsigned | C::Less | C::Neq>(args);
            case Z3_OP_SLT:
                return Abstract::compare<Ex::BV, C::Signed | C::Less | C::Neq>(args);
            case Z3_OP_UGT:
                return Abstract::compare<Ex::BV, C::Unsigned | C::Greater | C::Neq>(args);
            case Z3_OP_SGT:
                return Abstract::compare<Ex::BV, C::Signed | C::Greater | C::Neq>(args);

                // Bit-vectors
            case Z3_OP_BNUM:
                ASSERT_ARG_EMPTY(args);
                return Abstract::BV::num(b_obj);
            case Z3_OP_BNEG:
                return Abstract::neg<Ex::BV>(args);
            case Z3_OP_BADD:
                return Abstract::add(args);
            case Z3_OP_BSUB:
                return Abstract::sub(args);
            case Z3_OP_BMUL:
                return Abstract::mul(args);

                // BV Arithmetic
            case Z3_OP_BSDIV: // fallthrough
            case Z3_OP_BSDIV_I:
                return Abstract::div<true>(args);
            case Z3_OP_BUDIV: // fallthrough:
            case Z3_OP_BUDIV_I:
                return Abstract::div<false>(args);
            case Z3_OP_BSMOD:   // fallthrough
            case Z3_OP_BSREM:   // fallthrough
            case Z3_OP_BSMOD_I: // fallthrough
            case Z3_OP_BSREM_I:
                return Abstract::rem<true>(args);
            case Z3_OP_BUREM: // fallthrough
            case Z3_OP_BUREM_I:
                return Abstract::rem<false>(args);

                // BV Logic
            case Z3_OP_BAND:
                return Abstract::and_<Ex::BV>(args);
            case Z3_OP_BOR:
                return Abstract::or_<Ex::BV>(args);
            case Z3_OP_BNOT:
                return Abstract::not_<Ex::BV>(args);
            case Z3_OP_BXOR:
                return Abstract::xor_<Ex::BV>(args);

                // BV Bitwise Ops
            case Z3_OP_BSHL:
                return Abstract::shift<Shift::Left>(args);
            case Z3_OP_BASHR:
                return Abstract::shift<Shift::ArithmeticRight>(args);
            case Z3_OP_BLSHR:
                return Abstract::shift<Shift::LogicalRight>(args);
            case Z3_OP_EXT_ROTATE_LEFT:
                return Abstract::rotate<Mode::LR::Left>(args);
            case Z3_OP_EXT_ROTATE_RIGHT:
                return Abstract::rotate<Mode::LR::Right>(args);

                // BV Misc
            case Z3_OP_CONCAT:
                return Abstract::concat(args);
            case Z3_OP_SIGN_EXT:
                return Abstract::sign_ext(args, decl);
            case Z3_OP_ZERO_EXT:
                return Abstract::zero_ext(args, decl);
            case Z3_OP_EXTRACT:
                return Abstract::extract(args, b_obj);

                // FP Conversions
            case Z3_OP_FPA_TO_SBV:
                return Abstract::FP::to_bv<true>(args, decl);
            case Z3_OP_FPA_TO_UBV:
                return Abstract::FP::to_bv<false>(args, decl);
            case Z3_OP_FPA_TO_IEEE_BV:
                return Abstract::FP::to_ieee_bv(args);
            case Z3_OP_FPA_TO_FP:
                return Abstract::FP::to_fp(args);
            case Z3_OP_FPA_NUM:
                return Abstract::FP::num(b_obj);

                // FP Constants
            case Z3_OP_FPA_MINUS_ZERO:
                ASSERT_ARG_EMPTY(args);
                return Abstract::FP::zero<Sign::Minus>(b_obj);
            case Z3_OP_FPA_MINUS_INF:
                ASSERT_ARG_EMPTY(args);
                return Abstract::FP::inf<Sign::Minus>(b_obj);
            case Z3_OP_FPA_PLUS_ZERO:
                ASSERT_ARG_EMPTY(args);
                return Abstract::FP::zero<Sign::Plus>(b_obj);
            case Z3_OP_FPA_PLUS_INF:
                ASSERT_ARG_EMPTY(args);
                return Abstract::FP::inf<Sign::Plus>(b_obj);
            case Z3_OP_FPA_NAN:
                ASSERT_ARG_EMPTY(args);
                return Abstract::FP::nan(b_obj);

                // FP Comparisons
            case Z3_OP_FPA_EQ:
                return Abstract::eq<Ex::FP>(args);
            case Z3_OP_FPA_GT:
                return Abstract::compare<Ex::FP, C::Signed | C::Greater | C::Neq>(args);
            case Z3_OP_FPA_GE:
                return Abstract::compare<Ex::FP, C::Signed | C::Greater | C::Eq>(args);
            case Z3_OP_FPA_LT:
                return Abstract::compare<Ex::FP, C::Signed | C::Less | C::Neq>(args);
            case Z3_OP_FPA_LE:
                return Abstract::compare<Ex::FP, C::Signed | C::Less | C::Eq>(args);

                // FP Arithmetic
            case Z3_OP_FPA_ABS:
                return Abstract::abs(args);
            case Z3_OP_FPA_NEG:
                return Abstract::neg<Ex::FP>(args);
            case Z3_OP_FPA_ADD:
                return Abstract::FP::add(args);
            case Z3_OP_FPA_SUB:
                return Abstract::FP::sub(args);
            case Z3_OP_FPA_MUL:
                return Abstract::FP::mul(args);
            case Z3_OP_FPA_DIV:
                return Abstract::FP::div(args);

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

    /** Return a T given the decl_kind */
    template <typename T> T fp_const(const Z3_decl_kind &decl_kind) {
        static_assert(Utils::qualified_is_in<T, float, double>, "Unsupported fp type");
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
                throw Utils::Error::Unexpected::Usage(
                    WHOAMI_WITH_SOURCE "called with ba;d decl_kind: ", decl_kind);
        }
    }

    /** Return true if the expression is a z3 string */
    inline bool string_check(const z3::expr &b_obj) {
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

    /** Abstract a backend object into a primitive stored in a PrimVar */
    inline PrimVar dispatch_abstraction_to_prim(const z3::expr &b_obj) {
        Utils::affirm<Utils::Error::Unexpected::Size>(b_obj.num_args() == 0, WHOAMI_WITH_SOURCE
                                                      "Op should have no children");

        // Get switching variables
        const auto decl { b_obj.decl() };
        const auto decl_kind { decl.decl_kind() };

        // Switch on expr type
        switch (decl_kind) {
            default: {
                throw Error::Backend::Abstraction(
                    WHOAMI_WITH_SOURCE
                    "Z3 backend cannot abstract given op to primitive; decl_kind: ",
                    decl_kind, "\nThe z3 op with this sort is:\n\t", b_obj);
            }

            // @todo others

            // Boolean
            case Z3_OP_TRUE:
                return true;
            case Z3_OP_FALSE:
                return false;

            // Conversions
            case Z3_OP_BNUM: {
                const auto x { Abstract::BV::num_primtive(b_obj) };
                /** A local helper macro */
#define G_CASE(I)                                                                                 \
    case I:                                                                                       \
        return std::get<I>(x);
                switch (x.index()) {
                    G_CASE(0)
                    G_CASE(1)
                    G_CASE(2)
                    G_CASE(3)
                    G_CASE(4)
                    default:
                        throw Utils::Error::Unexpected::Unknown(WHOAMI_WITH_SOURCE, "Bad variant");
                }
#undef G_CASE
                static_assert(std::variant_size_v<decltype(x)> == 5,
                              "Switch-case statement needs to be modified");
            }
            case Z3_OP_FPA_NUM: {
                const std::variant<double, float> x { Abstract::FP::num_primitive(b_obj) };
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
                throw Utils::Error::Unexpected::NotSupported("Unsupported fp primitive width");
            }

            case Z3_OP_CONCAT: {
                Utils::affirm<Error::Backend::Abstraction>(
                    !Z3::rhfpu, WHOAMI_WITH_SOURCE
                    "rewriter.hi_fp_unspecified is set to false, this should not be triggered");
                const auto n { b_obj.num_args() };
                int res = 0; // @todo wrong
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
                        throw Error::Backend::Abstraction("Weird z3 model");
                    }
                    auto arg_int { Abstract::BV::num_primtive(arg) };
                    if (neg) {
                        arg_int = (1 << arg_size) - arg_int;
                    }
                    res <<= arg_size;
                    res |= arg_int;
                }
                return res;
            }
            case Z3_OP_FPA_TO_IEEE_BV: {
                Utils::affirm<Error::Backend::Abstraction>(
                    Z3::rhfpu, WHOAMI_WITH_SOURCE
                    "rewriter.hi_fp_unspecified is set to true, this should not be triggered");
#ifdef DEBUG
                Utils::affirm<Utils::Error::Unexpected::Size>(
                    b_obj.num_args() > 0, WHOAMI_WITH_SOURCE "num_args should be at least one!");
#endif
                b_obj.arg(0);
                // @todo fpToIEEEBV
            }

            // String
            case Z3_OP_INTERNAL: {
                Utils::affirm<Error::Backend::Abstraction>(string_check(b_obj), WHOAMI_WITH_SOURCE
                                                           "b_obj is not a string as expected");
                return Abstract::internal_primitive(b_obj, decl);
            }
        }
    }

} // namespace Backend::Z3::Private

#endif
