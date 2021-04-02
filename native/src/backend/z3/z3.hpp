/**
 * @file
 * @brief This file defines the z3 backend
 */
#ifndef __BACKEND_Z3_Z3_HPP__
#define __BACKEND_Z3_Z3_HPP__

#include "abstract.hpp"
#include "convert.hpp"

#include "../generic.hpp"


namespace Backend::Z3 {

    /** The solver type */
    using Solver = z3::Solver;

    /** The Z3 backend */
    class Z3 final : public Generic<BackendObj, Solver> {
      private:
        /********************************************************************/
        /*                          Representation                          */
        /********************************************************************/


        /** Thread local Z3 context */
        thread_local z3::Context context {}; // TODO: figure out if this is a pointer or what


        /********************************************************************/
        /*                        Function Overrides                        */
        /********************************************************************/


        /** This dynamic dispatcher converts expr into a backend object
         *  All arguments of expr that are not primitives have been
         *  pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         *  Warning: This function may internally do unchecked static casting, we permit this
         *  *only* if the cuid of the expression is of or derive from the type being cast to.
         */
        BOCPtr dispatch_conversion(const ExprRawPtr expr,
                                   std::vector<BOCPtr> &args) override final {

            // We define local macros below to enforce consistency
            // across 'trivial' ops to reduce copy-paste errors.

#define UNARY_CASE(OP, FN)                                                                        \
    case Op::OP::static_cuid: {                                                                   \
        auto ret { std::move(FN(*args.back())) };                                                 \
        args.pop_back();                                                                          \
        return ret;                                                                               \
    }

#define BINARY_DISPATCH(FN)                                                                       \
    const auto size = args.size();                                                                \
    auto ret { std::move(FN(*args[size - 2], *args[size - 1])) };                                 \
    args.resize(size - 2);                                                                        \
    return ret;

#define BINARY_CASE(OP, FN)                                                                       \
    case Op::OP::static_cuid: {                                                                   \
        BINARY_DISPATCH(FN);                                                                      \
    }

// Passing templated objects to macros can be messy since ','s are in both
// For simplicity and consistency we define a binary op macro for this case
#define BINARY_TEMPLATE_CASE(OP, FN, ...)                                                         \
    case Op::OP<__VA_ARGS__>::static_cuid: {                                                      \
        const auto &func = FN<__VA_ARGS__>;                                                       \
        BINARY_DISPATCH(func);                                                                    \
    }

#define INT_BINARY_CASE(OP, FN)                                                                   \
    case Op::OP::static_cuid: {                                                                   \
        static_assert(Op::is_int_binary<Op::OP>, WHOAMI "Op::" #OP "is not IntBinary");           \
        using To = Constants::CTSC<Op::IntBinary>;                                                \
        auto ret { std::move(FN(*args.back(), static_cast<To>(expr)->integer)) };                 \
        args.pop_back();                                                                          \
        return ret;                                                                               \
    }

#define MODE_BINARY_CASE(OP, FN)                                                                  \
    case Op::OP::static_cuid: {                                                                   \
        const auto size = args.size();                                                            \
        static_assert(Op::is_mode_binary<Op::OP>, WHOAMI "Op::" #OP "is not ModeBinary");         \
        using To = Constants::CTSC<Op::FP::ModeBinary>;                                           \
        auto ret { std::move(                                                                     \
            FN(static_cast<To>(expr)->mode, *args[size - 2], *args[size - 1])) };                 \
        args.resize(size - 2);                                                                    \
        return ret;                                                                               \
    }

#define TERNARY_CASE(OP, FN)                                                                      \
    case Op::OP::static_cuid: {                                                                   \
        const auto size = args.size();                                                            \
        auto ret { std::move(FN(*args[size - 3], *args[size - 2], *args[size - 1])) };            \
        args.resize(size - 3);                                                                    \
        return ret;                                                                               \
    }

#define FLAT_CASE(OP, FN)                                                                         \
    case Op::OP::static_cuid: {                                                                   \
        const auto a_size = args.size();                                                          \
        static_assert(Op::is_flat<Op::OP>, WHOAMI "Op::" #OP "is not Flat");                      \
        using To = Constants::CTSC<Op::Flat>;                                                     \
        const auto n = static_cast<To>(expr)->operands.size();                                    \
        ExprRawPtr fn_args[n];                                                                    \
        const auto first_n = a_size - n;                                                          \
        for (auto i = 0; i < n; ++i) {                                                            \
            fn_args[i] = *args[first_n + i];                                                      \
        }                                                                                         \
        auto ret { std::move(FN(n, fn_args)) };                                                   \
        args.resize(size - n);                                                                    \
        return ret;                                                                               \
    }
            // Create a converter
            Converter convert { context };

            // Switch on expr type
            switch (expr->op->cuid) {

                // This should never be hit
                default: {
                    using Usage = Utils::Error::Unexpected;
                    throw Err::IncorrectUsage(
                        WHOAMI_WITH_SOURCE
                        "Unknown expression op given to z3::dispatch_conversion."
                        "\nOp CUID: ",
                        expr->op->cuid);
                }

                    /************************************************/
                    /*              Top-Level Trivial               */
                    /************************************************/

                    // Unary

                    UNARY_CASE(Neg, convert.neg);
                    UNARY_CASE(Abs, convert.abs);
                    UNARY_CASE(Invert, convert.invert);
                    UNARY_CASE(Reverse, convert.reverse);

                    // IntBinary

                    INT_BINARY_CASE(SignExt, convert.signext);
                    INT_BINARY_CASE(ZeroExt, convert.zeroext);

                    // Binary

                    BINARY_CASE(Eq, convert.eq);

                    BINARY_TEMPLATE_CASE(Compare, convert.compare, true, true, true);
                    BINARY_TEMPLATE_CASE(Compare, convert.compare, true, true, false);
                    BINARY_TEMPLATE_CASE(Compare, convert.compare, true, false, true);
                    BINARY_TEMPLATE_CASE(Compare, convert.compare, true, false, false);
                    BINARY_TEMPLATE_CASE(Compare, convert.compare, false, true, true);
                    BINARY_TEMPLATE_CASE(Compare, convert.compare, false, true, false);
                    BINARY_TEMPLATE_CASE(Compare, convert.compare, false, false, true);
                    BINARY_TEMPLATE_CASE(Compare, convert.compare, false, false, false);

                    BINARY_CASE(Sub, convert.sub);

                    BINARY_TEMPLATE_CASE(Div, convert.div, true);
                    BINARY_TEMPLATE_CASE(Div, convert.div, false);

                    BINARY_CASE(Pow, convert.pow);

                    BINARY_TEMPLATE_CASE(Mod, convert.mod, true);
                    BINARY_TEMPLATE_CASE(Mod, convert.mod, false);

                    BINARY_TEMPLATE_CASE(Shift, convert.shift, true, true);
                    BINARY_TEMPLATE_CASE(Shift, convert.shift, true, false);
                    BINARY_TEMPLATE_CASE(Shift, convert.shift, false, true);
                    BINARY_TEMPLATE_CASE(Shift, convert.shift, false, false);

                    BINARY_TEMPLATE_CASE(Rotate, convert.rotate, true);
                    BINARY_TEMPLATE_CASE(Rotate, convert.rotate, false);

                    BINARY_CASE(Widen, convert.widen);
                    BINARY_CASE(Union, convert.union);
                    BINARY_CASE(Intersection, convert.intersection);
                    BINARY_CASE(Concat, convert.concat);

                    // Flat

                    FLAT_CASE(Add, convert.add);
                    FLAT_CASE(Mul, convert.mul);
                    FLAT_CASE(Or, convert.or);
                    FLAT_CASE(And, convert.and);
                    FLAT_CASE(Xor, convert.xor);

                    // Other

                    TERNARY_CASE(If, convert.if);

                case Op::Extract::static_cuid: {
                    using To = Constants::CTSC<Op::Extract>;
                    auto ret { std::move(convert.extract(
                        static_cast<To>(expr)->high, static_cast<To>(expr)->low, *args.back())) };
                    args.pop_back();
                    return ret;
                }
                case Op::Literal::static_cuid: {
                    break; // TODO
                }
                case Op::Symbol::static_cuid: {
                    break; // TODO
                }

                    /************************************************/
                    /*                  FP Trivial                  */
                    /************************************************/

                    // Unary

                    UNARY_CASE(FP::ToIEEEBV, convert.fp_to_ieee_bv);
                    UNARY_CASE(FP::IsInf, convert.fp_is_inf);
                    UNARY_CASE(FP::IsNan, convert.fp_is_nan);

                    // Binary

                    BINARY_CASE(FP::NE, convert.fp_ne);

                    // Mode Binary

                    MODE_BINARY_CASE(FP::Add, convert.fp_add)
                    MODE_BINARY_CASE(FP::Sub, convert.fp_sub)
                    MODE_BINARY_CASE(FP::Div, convert.fp_div)

                    // Ternary

                    TERNARY_CASE(FP::FP, convert.fp_fp)

                    // Other

                case Op::FP::ToBV::static_cuid: {
                    using To = Constants::CTSC<Op::FP::ToBV>;
                    auto ret { std::move(
                        convert.extract(static_cast<To>(expr)->mode, *args.back())) };
                    args.pop_back();
                    return ret;
                }

                    /************************************************/
                    /*                String Trivial                */
                    /************************************************/

                    // Unary

                    UNARY_CASE(String::IsDigit, convert.string_is_digit);
                    UNARY_CASE(String::FromInt, convert.string_from_int);
                    UNARY_CASE(String::Unit, convert.string_unit);

                    // Int Binary

                    INT_BINARY_CASE(String::ToInt, convert.string_to_int);
                    INT_BINARY_CASE(String::Len, convert.string_len);

                    // Binary

                    BINARY_CASE(String::Contains, convert.string_contains);
                    BINARY_CASE(String::PrefixOf, convert.string_prefix_of);
                    BINARY_CASE(String::SuffixOf, convert.string_suffix_of);

                    // Ternary

                    TERNARY_CASE(String::Replace, convert.string_replace);

                    // Other

                    TERNARY_CASE(String::SubString, convert.sub_string)

                case Op::String::IndexOf::static_cuid: {
                    using To = Constants::CTSC<Op::String::IndexOf>;
                    const auto size = args.size();
                    auto ret {
                        std::move(convert.if (*args[size - 2], *args[size - 1],
                                              static_cast<To>(expr)->start_index))
                    };
                    args.resize(size - 2);
                    return ret;
                }
            }

                // Cleanup
#undef UNARY_CASE
#undef BINARY_DISPATCH
#undef BINARY_CASE
#undef BINARY_TEMPLATE_CASE
#undef INT_BINARY_CASE
#undef MODE_BINARY_CASE
#undef TERNARY_CASE
#undef FLAT_CASE
        }
    };

} // namespace Backend::Z3

#endif
