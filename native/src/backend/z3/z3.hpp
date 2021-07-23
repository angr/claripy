/**
 * @file
 * @brief This file defines the Z3 backend
 */
#ifndef R_BACKEND_Z3_Z3_HPP_
#define R_BACKEND_Z3_Z3_HPP_

#include "abstract.hpp"
#include "bool_tactic.hpp"
#include "convert.hpp"

#include "../../error.hpp"
#include "../generic.hpp"


namespace Backend::Z3 {

    /** The Z3 backend */
    class Z3 final : public Z3Super {
        static_assert(!use_apply_annotations, "Z3 objects do not support holding annotations");

      public:
        /********************************************************************/
        /*                     Small Function Overrides                     */
        /********************************************************************/

        /** Destructor */
        ~Z3() noexcept override = default;

        /** Clear caches to decrease memory pressure
         *  Note: Does not clear translocation data
         */
        inline void downsize() override {
            Z3Super::downsize();
            is_true_cache.scoped_unique().first.clear();
            is_false_cache.scoped_unique().first.clear();
        }

        /** Clears translocation data */
        inline void clear_persistent_data() override {
            symbol_annotation_translocation_data.clear();
        }

        /** Create a tls solver */
        [[nodiscard]] inline virtual std::shared_ptr<void> new_tls_solver() const override final {
            return { std::make_shared<z3::solver>(Private::tl_ctx) };
        }

        /** The name of this backend */
        [[nodiscard]] inline const char *name() const noexcept override final { return "z3"; }

        /** Return true if expr is always true
         *  expr may not be nullptr
         */
        inline bool is_true(const Expression::RawPtr &expr) {
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
        inline bool is_false(const Expression::RawPtr &expr) {
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

        /** The method used to simplify z3 boolean expressions */
        static inline z3::expr bool_simplify(const z3::expr &expr) {
            thread_local BoolTactic bt;
            return bt(expr);
        }

        /** Simplify the given expression
         *  expr may not be nullptr
         */
        inline Expression::BasePtr simplify_raw(const Expression::RawPtr expr) override final {
            UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
            namespace Ex = Expression;
            switch (expr->cuid) {
                case Ex::Bool::static_cuid: {
                    auto b_obj { convert(expr) };
                    b_obj = bool_simplify(b_obj);
                    return abstract(b_obj);
                }
                case Ex::BV::static_cuid: {
                    auto b_obj = convert(expr);
                    b_obj = b_obj.simplify();
                    return abstract(b_obj);
                }
                default: {
#ifdef DEBUG
                    const auto ret { Ex::find(expr->hash) };
                    using Err = Utils::Error::Unexpected::HashCollision;
                    Utils::affirm<Err>(ret.get() == expr, WHOAMI_WITH_SOURCE);
                    return ret;
#else
                    return Ex::find(expr->hash);
#endif
                }
            }
        }

      private:
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
        /*                          Representation                          */
        /********************************************************************/


        /** is_true cache
         *  Map an expression hash to the result of is_true
         */
        inline static TSM<std::map<Hash::Hash, const bool>> is_true_cache {};

        /** is_false cache
         *  Map an expression hash to the result of is_false
         */
        inline static TSM<std::map<Hash::Hash, const bool>> is_false_cache {};

        /** Stores a symbol's annotations to be translocated from the pre-conversion expression
         *  to the post-abstraction expression symbol of the same name.
         */
        inline static thread_local std::map<std::string, Expression::Base::SPAV>
            symbol_annotation_translocation_data {};


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
            using Shift = Mode::Shift;

            // Switch on expr type
            switch (expr->op->cuid) {

                // This should never be hit
                default: {
                    throw Utils::Error::Unexpected::NotSupported(
                        WHOAMI_WITH_SOURCE "Unknown expression op given.\nOp CUID: ",
                        expr->op->cuid);
                }

                    // Unsupported ops
                case Op::Widen::static_cuid:           // fallthrough
                case Op::Union::static_cuid:           // fallthrough
                case Op::FP::FP::static_cuid:          // fallthrough
                case Op::String::IsDigit::static_cuid: // fallthrough
                case Op::Intersection::static_cuid: {
                    throw Error::Backend::Unsupported(
                        WHOAMI_WITH_SOURCE "Unsupported expression op given.\nOp CUID: ",
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
                    return Convert::symbol(expr, symbol_annotation_translocation_data);
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

        /** Abstract a backend object into a claricpp expression */
        AbstractionVariant
        dispatch_abstraction(const z3::expr &b_obj,
                             std::vector<AbstractionVariant> &args) override final {

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
                    return Abstract::uninterpreted(b_obj, decl, args,
                                                   symbol_annotation_translocation_data);
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
    };

} // namespace Backend::Z3

#endif
