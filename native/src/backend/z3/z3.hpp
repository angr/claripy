/**
 * @file
 * @brief This file defines the Z3 backend
 */
#ifndef R_BACKEND_Z3_Z3_HPP_
#define R_BACKEND_Z3_Z3_HPP_

#include "abstract.hpp"
#include "convert.hpp"
#include "tl_ctx.hpp"

#include "../../error.hpp"
#include "../generic.hpp"

#include <memory>


namespace Backend::Z3 {

    /** The Z3 backend */
    class Z3 final : public Generic<z3::expr, false> {
        /** Z3 parent class */
        using Super = Generic<z3::expr, false>;

      public:
        /********************************************************************/
        /*                     Small Function Overrides                     */
        /********************************************************************/

        /** Destructor */
        ~Z3() noexcept override = default;

        /** Clear caches to decrease memory pressure */
        void downsize() override {
            Super::downsize();
            is_true_cache.scoped_unique().first.clear();
            is_false_cache.scoped_unique().first.clear();
        }

        /** Create a tls solver */
        [[nodiscard]] virtual std::shared_ptr<void> new_tls_solver() const override final {
            return { std::make_shared<z3::solver>(Private::tl_ctx) };
        }

        /** The name of this backend */
        [[nodiscard]] const char *name() const noexcept override final { return "z3"; }

        /** Return true if expr is always true
         *  expr may not be nullptr
         */
        bool is_true(const Expression::RawPtr &expr) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
            auto [in_cache, res] { get_from_cache(is_true_cache, expr->hash) };
            if (in_cache) {
                return res;
            }
            const bool ret { convert(expr).is_true() };
            is_true_cache.scoped_unique().first.emplace(expr->hash, ret);
            is_false_cache.scoped_unique().first.emplace(expr->hash, ret);
            return ret;
        }

        /** Return true if expr is always false
         *  expr may not be nullptr
         */
        bool is_false(const Expression::RawPtr &expr) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
            auto [in_cache, res] { get_from_cache(is_false_cache, expr->hash) };
            if (in_cache) {
                return res;
            }
            const bool ret { convert(expr).is_true() };
            is_false_cache.scoped_unique().first.emplace(expr->hash, ret);
            is_true_cache.scoped_unique().first.emplace(expr->hash, ret);
            return ret;
        }

        /** Simplify the given expression
         *  expr may not be nullptr
         *  @todo: Currently this is stubbed, it needs to be implemented
         */
        Expression::BasePtr simplify(const Expression::RawPtr expr) override final {
            UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
            (void) expr;
            throw Utils::Error::Unexpected::NotSupported("This has yet to be implemented"); // TODO
        }

      private:
        /** A function that checks that *e is a subclass of T if DEBUG is enabled
         *  If not, a type exception prefiexed by with message args... will be raised
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

        /** An abbreviation for Utils::ThreadSafe::Mutable */
        template <typename T> using TSM = Utils::ThreadSafe::Mutable<T>;

        // Caches

        /** A helper function that tries to get an object from a cache
         *  Returns a pair; the first value is a boolean that stores if it was found
         *  The second value is the value that was found, or default constructed if not found
         *  Note that the second value is copied to ensure thread safety
         */
        template <typename Key, typename Value>
        static std::pair<bool, Value> get_from_cache(const TSM<std::map<Key, Value>> &tsm_cache,
                                                     const Key &key) {
            auto [cache, _] = tsm_cache.scoped_shared();
            if (const auto lookup { cache.find(key) }; lookup != cache.end()) {
                return { true, lookup->second };
            }
            return { false, {} };
        }

        /** is_true cache
         *  Map an expression hash to the result of is_true
         */
        inline static TSM<std::map<Hash::Hash, const bool>> is_true_cache {};

        /** is_false cache
         *  Map an expression hash to the result of is_false
         */
        inline static TSM<std::map<Hash::Hash, const bool>> is_false_cache {};

        /** Verify the container contains at least n elements
         *  In debug mode verifies that the last n elements are not nullptr
         */
        template <typename T, typename... Args>
        inline void check_vec_usage(const T &c, const Constants::UInt n, Args &&...args) {
            namespace Err = Utils::Error::Unexpected;
            Utils::affirm<Err::Size>(c.size() >= n, std::forward<Args>(args)...,
                                     "container is too small to access ", n, " elements");
#ifdef DEBUG
            const auto last { c.size() - 1 };
            for (Constants::UInt i { 0 }; i < n; ++i) {
                Utils::affirm<Err::Null>(c[last - i] != nullptr, std::forward<Args>(args)...,
                                         "container element cannot be nullptr");
            }
#endif
        }


        /********************************************************************/
        /*                 Large Dispatch Function Overrides                */
        /********************************************************************/

      public:
        /** This dynamic dispatcher converts expr into a backend object
         *  All arguments of expr that are not primitives have been
         *  pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         *  expr may not be nullptr
         *  Warning: This function may internally do unchecked static casting, we permit this
         *  *only* if the cuid of the expression is of or derive from the type being cast to.
         */
        z3::expr dispatch_conversion(const Expression::RawPtr expr,
                                     std::vector<const z3::expr *> &args) override final {
            UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
            UTILS_AFFIRM_NOT_NULL_DEBUG(expr->op); // Sanity check

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
            using Shft = Mode::Shift;

            // Switch on expr type
            switch (expr->op->cuid) {

                // This should never be hit
                default: {
                    throw Utils::Error::Unexpected::NotSupported(
                        WHOAMI_WITH_SOURCE "Unknown expression op given to ", __func__,
                        "\nOp CUID: ", expr->op->cuid);
                }

                // Unsupported ops
                case Op::Widen::static_cuid:           // fallthrough
                case Op::Union::static_cuid:           // fallthrough
                case Op::String::IsDigit::static_cuid: // fallthrough
                case Op::Intersection::static_cuid: {
                    throw Error::Backend::Unsupported(WHOAMI_WITH_SOURCE
                                                      "Unknown expression op given to ",
                                                      __func__, "\nOp CUID: ", expr->op->cuid);
                }

                    /************************************************/
                    /*              Top-Level Trivial               */
                    /************************************************/

                    // Unary

                    UNARY_CASE(Neg, Convert::neg);
                    UNARY_CASE(Abs, Convert::abs);
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
                    BINARY_TEMPLATE_CASE(Compare, Convert::compare,
                                         Cmp::Signed | Cmp::Less | Cmp::Eq);
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

                    BINARY_CASE(Pow, Convert::pow);

                    BINARY_TEMPLATE_CASE(Mod, Convert::mod, true);
                    BINARY_TEMPLATE_CASE(Mod, Convert::mod, false);

                    // Logic / left is not supported a valid mode
                    BINARY_TEMPLATE_CASE(Shift, Convert::shift, Shft::Arithmetic | Shft::Left);
                    BINARY_TEMPLATE_CASE(Shift, Convert::shift, Shft::Arithmetic | Shft::Right);
                    BINARY_TEMPLATE_CASE(Shift, Convert::shift, Shft::Logical | Shft::Right);

                    BINARY_TEMPLATE_CASE(Rotate, Convert::rotate, true);
                    BINARY_TEMPLATE_CASE(Rotate, Convert::rotate, false);

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
                    return Convert::symbol(expr);
                }

                    /************************************************/
                    /*                  FP Trivial                  */
                    /************************************************/

                    // Unary

                    UNARY_CASE(FP::ToIEEEBV, Convert::FP::to_ieee_bv);
                    UNARY_CASE(FP::IsInf, Convert::FP::is_inf);
                    UNARY_CASE(FP::IsNaN, Convert::FP::is_nan);

                    // Mode Binary

                    MODE_BINARY_CASE(FP::Add, Convert::FP::add);
                    MODE_BINARY_CASE(FP::Sub, Convert::FP::sub);
                    MODE_BINARY_CASE(FP::Mul, Convert::FP::mul);
                    MODE_BINARY_CASE(FP::Div, Convert::FP::div);

                    // Ternary

                    TERNARY_CASE(FP::FP, Convert::FP::fp);

                    // Other

/** A local macro used for consistency */
#define TO_BV_CASE(TF)                                                                            \
    case Op::FP::ToBV<TF>::static_cuid: {                                                         \
        debug_assert_dcast<Expression::Bits>(expr, WHOAMI_WITH_SOURCE "FP::ToBV has no length");  \
        using ToBV = Constants::CTSC<Op::FP::ToBV<false>>;                                        \
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
                    auto ret { Convert::FP::from_not_2s_complement_bv(*args.back(),
                                                                      cast_op->width) };
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

        /** Abstract a backend object into a claricpp expression
         *  b_obj may not be nullptr
         */
        AbstractionVariant
        dispatch_abstraction(Constants::CTSC<z3::expr> b_obj,
                             std::vector<Expression::BasePtr> &args) override final {
            UTILS_AFFIRM_NOT_NULL_DEBUG(b_obj);
            (void) args;

            // Get switching variables
            const auto decl { b_obj->decl() };
            const auto decl_kind { decl.decl_kind() };
            const auto sort_kind { b_obj->get_sort().sort_kind() };

            // For brevity
            using Cmp = Mode::Compare;
            using Shft = Mode::Shift;

/** A local macro used for error checking in debug mode */
#define ASSERT_EMPTY_DEBUG(X)                                                                     \
    Utils::affirm<Utils::Error::Unexpected::Size>((X).empty(),                                    \
                                                  WHOAMI_WITH_SOURCE "container is not empty");

            // Switch on expr type
            switch (decl_kind) {

                // Unsupported op
                default: {
                    throw Error::Backend::Abstraction(WHOAMI_WITH_SOURCE "Unknown z3 op given to ",
                                                      __func__, "\nOp decl_kind: ", decl_kind);
                }

                // Boolean
                case Z3_OP_TRUE:
                    ASSERT_EMPTY_DEBUG(args);
                    return Abstract::bool_<true>;
                case Z3_OP_FALSE:
                    ASSERT_EMPTY_DEBUG(args);
                    return Abstract::bool_<false>;
                case Z3_OP_EQ:
                case Z3_OP_DISTINCT:
                case Z3_OP_ITE:
                case Z3_OP_AND:
                case Z3_OP_OR:
                case Z3_OP_IFF:
                case Z3_OP_XOR:
                case Z3_OP_NOT:
                case Z3_OP_IMPLIES:

                // Arithmetic
                case Z3_OP_LE:
                case Z3_OP_GE:
                case Z3_OP_LT:
                case Z3_OP_GT:
                case Z3_OP_ADD:
                case Z3_OP_SUB:
                case Z3_OP_UMINUS:
                case Z3_OP_MUL:
                case Z3_OP_DIV:
                case Z3_OP_IDIV:
                case Z3_OP_REM:
                case Z3_OP_MOD:
                case Z3_OP_POWER:

                // Bit-vectors
                case Z3_OP_BNUM:
                case Z3_OP_BNEG:
                case Z3_OP_BADD:
                case Z3_OP_BSUB:
                case Z3_OP_BMUL:

                    // BV Arithmetic
                case Z3_OP_BSDIV:
                case Z3_OP_BUDIV:
                case Z3_OP_BSREM:
                case Z3_OP_BUREM:
                case Z3_OP_BSMOD:
                case Z3_OP_BSDIV_I:
                case Z3_OP_BUDIV_I:
                case Z3_OP_BSREM_I:
                case Z3_OP_BUREM_I:
                case Z3_OP_BSMOD_I:

                // Comparisons
                case Z3_OP_ULEQ:
                case Z3_OP_SLEQ:
                case Z3_OP_UGEQ:
                case Z3_OP_SGEQ:
                case Z3_OP_ULT:
                case Z3_OP_SLT:
                case Z3_OP_UGT:
                case Z3_OP_SGT:

                    // BV Logic
                case Z3_OP_BAND:
                case Z3_OP_BOR:
                case Z3_OP_BNOT:
                case Z3_OP_BXOR:

                    // BV Misc
                case Z3_OP_CONCAT:
                case Z3_OP_SIGN_EXT:
                case Z3_OP_ZERO_EXT:
                case Z3_OP_EXTRACT:
                case Z3_OP_REPEAT:

                    // BV Bitwise ops
                case Z3_OP_BSHL:
                case Z3_OP_BLSHR:
                case Z3_OP_BASHR:
                case Z3_OP_EXT_ROTATE_LEFT:
                case Z3_OP_EXT_ROTATE_RIGHT:

                    // FP Conversions
                case Z3_OP_FPA_TO_SBV:
                case Z3_OP_FPA_TO_UBV:
                case Z3_OP_FPA_TO_IEEE_BV:
                case Z3_OP_FPA_TO_FP:
                case Z3_OP_FPA_NUM:

                    // FP Constants
                case Z3_OP_FPA_MINUS_ZERO:
                case Z3_OP_FPA_MINUS_INF:
                case Z3_OP_FPA_PLUS_ZERO:
                case Z3_OP_FPA_PLUS_INF:
                case Z3_OP_FPA_NAN:

                // FP Comparisons
                case Z3_OP_FPA_EQ:
                case Z3_OP_FPA_GT:
                case Z3_OP_FPA_GE:
                case Z3_OP_FPA_LT:
                case Z3_OP_FPA_LE:

                    // FP arithmetic
                case Z3_OP_FPA_ABS:
                case Z3_OP_FPA_NEG:
                case Z3_OP_FPA_ADD:
                case Z3_OP_FPA_SUB:
                case Z3_OP_FPA_MUL:
                case Z3_OP_FPA_DIV:

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

                    // Special z3 ops
                case Z3_OP_INTERNAL:
                case Z3_OP_UNINTERPRETED:

// Cleanup
#undef ASSERT_EMPTY_DEBUG
            }

            // TODO
            return { nullptr };
        }
    };

} // namespace Backend::Z3

#endif
