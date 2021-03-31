/**
 * @file
 * @brief This file defines the z3 backend
 */
#ifndef __BACKEND_Z3_HPP__
#define __BACKEND_Z3_HPP__

#include "generic.hpp"


namespace Backend::Z3 {

    /** The Z3 backend */
    class Z3 final : public Generic</* TODO */> {
      private:
        template <typename T> inline bool is_T(const ExprRawPtr expr) {
            using ConstT = Constants::CTSC<T>;
            return dynamic_cast<ConstT>(expr) != nullptr;
        }

        template <template <bool> typename T> inline bool is_T(const ExprRawPtr expr) {
            return is_T<T<true>> || is_T<T<false>>;
        }

        /** This dynamic dispatcher converts expr into a backend object
         *  All arguments of expr that are not primitives have been
         *  pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         */
        BOCPtr dispatch_conversion(const ExprRawPtr expr,
                                   std::vector<BOCPtr> &args) override final {

            // We define local macros below to enforce consistency
            // across 'trivial' ops to reduce copy-paste errors.

#define UNARY_CASE(OP, FN)                                                                        \
case Op::OP::static_cuid:                                                                         \
    auto ret { std::move(FN(*args.back())) };                                                     \
    args.pop_back();                                                                              \
    return ret;

#define BINARY_DISPATCH(FN)                                                                       \
    const auto size = args.size();                                                                \
    auto ret { std::move(FN(*args[size - 2], *args[size - 1])) };                                 \
    args.resize(size - 2);                                                                        \
    return ret

#define BINARY_CASE(OP, FN)                                                                       \
case Op::OP::static_cuid:                                                                         \
    BINARY_DISPATCH(FN)

// Passing templated objects to macros can be messy since ','s are in both
// For simplicity and consistency we define a binary op macro for this case
#define BINARY_TEMPLATE_CASE(OP, FN, ...)                                                         \
case Op::OP<__VA_ARGS__>::static_cuid:                                                            \
    const auto &func = FN<__VA_ARGS__>;                                                           \
    BINARY_DISPATCH(func);

#define INT_BINARY_CASE(OP, FN)                                                                   \
case Op::OP::static_cuid:                                                                         \
    using To = Constants::CTSC<Op::IntBinary>;                                                    \
    auto ret { std::move(FN(*args.back(), static_cast<To>(expr)->integer)) };                     \
    args.pop_back();                                                                              \
    return ret

#define MODE_BINARY_CASE(OP, FN)                                                                  \
case Op::OP::static_cuid:                                                                         \
    const auto size = args.size();                                                                \
    using To = Constants::CTSC<Op::FP::ModeBinary>;                                               \
    auto ret { std::move(FN(static_cast<To>(expr)->mode, *args[size - 2], *args[size - 1])) };    \
    args.resize(size - 2);                                                                        \
    return ret

#define TERNARY_CASE(OP, FN)                                                                      \
case Op::OP::static_cuid:                                                                         \
    const auto size = args.size();                                                                \
    auto ret { std::move(FN(*args[size - 3], *args[size - 2], *args[size - 1])) };                \
    args.resize(size - 3);                                                                        \
    return ret

#define FLAT_CASE(OP, FN)                                                                         \
case Op::OP::static_cuid:                                                                         \
    const auto a_size = args.size();                                                              \
    using To = Constants::CTSC<Op::Flat>;                                                         \
    const auto n = static_cast<To>(expr)->operands.size();                                        \
    ExprRawPtr fn_args[n];                                                                        \
    const auto first_n = a_size - n;                                                              \
    for (auto i = 0; i < n; ++i) {                                                                \
        fn_args[i] = *args[first_n + i];                                                          \
    }                                                                                             \
    auto ret { std::move(FN(n, fn_args)) };                                                       \
    args.resize(size - n);                                                                        \
    return ret

            // Switch on expr type
            switch (expr->op->cuid) {

            // This should never be hit
            default:
                using Usage = Utils::Error::Unexpected;
                throw Err::IncorrectUsage(WHOAMI_WITH_SOURCE
                                          "Unknown expression op given to z3::dispatch_conversion."
                                          "\nOp CUID: ",
                                          expr->op->cuid);

                /************************************************/
                /*              Top-Level Trivial               */
                /************************************************/

                // Unary

                UNARY_CASE(Neg, convert_neg);
                UNARY_CASE(Abs, convert_abs);
                UNARY_CASE(Invert, convert_invert);
                UNARY_CASE(Reverse, convert_reverse);

                // IntBinary

                INT_BINARY_CASE(SignExt, convert_signext);
                INT_BINARY_CASE(ZeroExt, convert_zeroext);

                // Binary

                BINARY_CASE(Eq, convert_eq);

                BINARY_TEMPLATE_CASE(Compare, convert_compare, true, true, true);
                BINARY_TEMPLATE_CASE(Compare, convert_compare, true, true, false);
                BINARY_TEMPLATE_CASE(Compare, convert_compare, true, false, true);
                BINARY_TEMPLATE_CASE(Compare, convert_compare, true, false, false);
                BINARY_TEMPLATE_CASE(Compare, convert_compare, false, true, true);
                BINARY_TEMPLATE_CASE(Compare, convert_compare, false, true, false);
                BINARY_TEMPLATE_CASE(Compare, convert_compare, false, false, true);
                BINARY_TEMPLATE_CASE(Compare, convert_compare, false, false, false);

                BINARY_CASE(Sub, convert_sub);

                BINARY_TEMPLATE_CASE(Div, convert_div, true);
                BINARY_TEMPLATE_CASE(Div, convert_div, false);

                BINARY_CASE(Pow, convert_pow);

                BINARY_TEMPLATE_CASE(Mod, convert_mod, true);
                BINARY_TEMPLATE_CASE(Mod, convert_mod, false);

                BINARY_TEMPLATE_CASE(Shift, convert_shift, true, true);
                BINARY_TEMPLATE_CASE(Shift, convert_shift, true, false);
                BINARY_TEMPLATE_CASE(Shift, convert_shift, false, true);
                BINARY_TEMPLATE_CASE(Shift, convert_shift, false, false);

                BINARY_TEMPLATE_CASE(Rotate, convert_rotate, true);
                BINARY_TEMPLATE_CASE(Rotate, convert_rotate, false);

                BINARY_CASE(Widen, convert_widen);
                BINARY_CASE(Union, convert_union);
                BINARY_CASE(Intersection, convert_intersection);
                BINARY_CASE(Concat, convert_concat);

                // Flat

                FLAT_CASE(Add, convert_add);
                FLAT_CASE(Mul, convert_mul);
                FLAT_CASE(Or, convert_or);
                FLAT_CASE(And, convert_and);
                FLAT_CASE(Xor, convert_xor);

                /************************************************/
                /*            Top-Level Non-Trivial             */
                /************************************************/

            case Op::Extract::static_cuid:
                break; // TODO
            case Op::If::static_cuid:
                break; // TODO
            case Op::Literal::static_cuid:
                break; // TODO
            case Op::Symbol::static_cuid:
                break; // TODO

                /************************************************/
                /*                  FP Trivial                  */
                /************************************************/

                // Unary

                UNARY_CASE(FP::ToIEEEBV, convert_fp_to_ieee_bv);
                UNARY_CASE(FP::IsInf, convert_fp_is_inf);
                UNARY_CASE(FP::IsNan, convert_fp_is_nan);

                // Binary

                BINARY_CASE(FP::NE, convert_fp_ne);

                // Mode Binary

                MODE_BINARY_CASE(FP::Add, convert_fp_add)
                MODE_BINARY_CASE(FP::Sub, convert_fp_sub)
                MODE_BINARY_CASE(FP::Div, convert_fp_div)

                // Ternary

                TERNARY_CASE(FP::FP, convert_fp_fp)

                /************************************************/
                /*                FP Non-Trivial                */
                /************************************************/

            case Op::FP::ToBV::static_cuid:
                break; // TODO

                /************************************************/
                /*                String Trivial                */
                /************************************************/

                // Unary

                UNARY_CASE(String::IsDigit, convert_string_is_digit);
                UNARY_CASE(String::FromInt, convert_string_from_int);
                UNARY_CASE(String::Unit, convert_string_unit);

                // Int Binary

                INT_BINARY_CASE(String::ToInt, convert_string_to_int);
                INT_BINARY_CASE(String::Len, convert_string_len);

                // Binary

                BINARY_CASE(String::Contains, convert_string_contains);
                BINARY_CASE(String::PrefixOf, convert_string_prefix_of);
                BINARY_CASE(String::SuffixOf, convert_string_suffix_of);

                // Ternary

                TERNARY_CASE(String::Replace, convert_string_replace);

                /************************************************/
                /*              String Non-Trivial              */
                /************************************************/

            case Op::String::IndexOf::static_cuid:
                break; // TODO
            case Op::String::SubString::static_cuid:
                break; // TODO
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

        /** Z3 context */
        thread_local z3::Context context {};
        // make z3::context()

        // Constructor, make tls context as member variable
    };

} // namespace Backend::Z3

#endif
