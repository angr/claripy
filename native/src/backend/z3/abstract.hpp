/**
 * @file
 * @brief This file defines how the Z3 backend converts Z3 ASTs into Claricpp Expressions
 */
#ifndef R_BACKEND_Z3_ABSTRACT_HPP_
#define R_BACKEND_Z3_ABSTRACT_HPP_

#include "constants.hpp"
#include "tl_ctx.hpp"
#include "width.hpp"

#include "../../create.hpp"

#include <cmath>
#include <limits>


/** A local macro used for length checking the number of children in a container */
#define ASSERT_ARG_LEN(X, N)                                                                      \
    Utils::affirm<Utils::Error::Unexpected::Size>(                                                \
        (X).size() == (N), WHOAMI_WITH_SOURCE "Op ", __func__,                                    \
        " should have " #N " children, but instead has: ", (X).size());

/** A local macro used for adding a case for a given type
 *  Func must be take in T as its only template argument
 */
#define TYPE_CASE(TYPE, FUNC, ...)                                                                \
    case Expression::TYPE::static_cuid:                                                           \
        return FUNC<Expression::TYPE>(__VA_ARGS__);

/** A local macro used for adding a default type case that throws an exception */
#define DEFAULT_TYPE_CASE(BAD_CUID)                                                               \
    default:                                                                                      \
        throw Utils::Error::Unexpected::Type(WHOAMI_WITH_SOURCE,                                  \
                                             "Unexpected type detected. CUID: ", (BAD_CUID));

/** A string explaining why this file refuses to abstract unknown floating point values */
#define REFUSE_FP_STANDARD                                                                        \
    "Refusing to use unknown point standard as the rules about bit manipulation on this "         \
    "standard may differ from expected."

/** A local macro for getting the X'th element of 'args' as an expression */
#define GET_EARG(I) std::get<Expression::BasePtr>(args[(I)])

// Macros for each op category

/** A local macro used for calling a basic unary expression
 *  Assumes the arguments array is called args
 *  FUNC may *not* have commas in it
 */
#define UNARY(FUNC)                                                                               \
    ASSERT_ARG_LEN(args, 1);                                                                      \
    return FUNC(GET_EARG(0));

/** A local macro used for calling a basic binary expression
 *  Assumes the arguments array is called args and decl is called decl
 *  FUNC may *not* have commas in it
 */
#define UINT_BINARY(FUNC)                                                                         \
    ASSERT_ARG_LEN(args, 1);                                                                      \
    return FUNC(GET_EARG(0), Utils::widen<Constants::UInt, true>(                                 \
                                 Z3_get_decl_int_parameter(Private::tl_ctx, decl, 0)));

/** A local macro used for calling a basic binary expression
 *  Assumes the arguments array is called args
 *  FUNC may *not* have commas in it
 */
#define BINARY(FUNC)                                                                              \
    ASSERT_ARG_LEN(args, 2);                                                                      \
    return FUNC(GET_EARG(0), GET_EARG(1));

/** A local macro used for calling a basic mode binary expression
 *  Assumes the arguments array is called args
 *  FUNC may *not* have commas in it
 */
#define MODE_BINARY(FUNC)                                                                         \
    ASSERT_ARG_LEN(args, 3);                                                                      \
    return FUNC(GET_EARG(1), GET_EARG(2), std::get<Mode::FP::Rounding>(args[0]));

/** A local macro used for calling a basic flat expression generated from only 2 arguments
 *  Assumes the arguments array is called args
 *  FUNC may *not* have commas in it
 */
#define FLAT_BINARY(FUNC)                                                                         \
    ASSERT_ARG_LEN(args, 2);                                                                      \
    return FUNC({ std::move(GET_EARG(0)), std::move(GET_EARG(1)) });


namespace Backend::Z3::Abstract {

    /** The 'args' array type */
    using ArgsVec = std::vector<Z3Super::AbstractionVariant>;

    /**********************************************************/
    /*                        General                         */
    /**********************************************************/

    /** Abstraction function for Z3_OP_INTERNAL to a primitive */
    inline std::string internal_primitive(const z3::expr &b, const z3::func_decl &decl) {
        const auto &ctx { Private::tl_ctx };
        if (UNLIKELY((Z3_get_decl_num_parameters(ctx, decl) != 1) ||
                     (Z3_get_decl_parameter_kind(ctx, decl, 0) != Z3_PARAMETER_SYMBOL))) {
            throw Error::Backend::Abstraction("Weird Z3 model (Type 1).", b);
        }
        const auto symb { Z3_get_decl_symbol_parameter(ctx, decl, 0) };
        if (UNLIKELY(Z3_get_symbol_kind(ctx, symb) != Z3_STRING_SYMBOL)) {
            throw Error::Backend::Abstraction("Weird Z3 model (Type 2).", b);
        }
        return { Z3_get_symbol_string(ctx, symb) };
    }

    /** Abstraction function for Z3_OP_INTERNAL */
    inline Expression::BasePtr internal(const z3::expr &b, const z3::func_decl &decl) {
        return Create::literal(internal_primitive(b, decl));
    }

    /** Abstraction function for Z3_OP_UNINTERPRETED */
    inline Expression::BasePtr uninterpreted(const z3::expr &b_obj, const z3::func_decl &decl,
                                             const ArgsVec &args, SymAnTransData &satd) {
        const auto sort { b_obj.get_sort() };
        // If b_obj is a symbolic value
        if (LIKELY(args.empty())) {
            // Gather info
            std::string name { decl.name().str() };
            switch (sort.sort_kind()) {
                case Z3_BV_SORT: {
                    const auto bl { sort.bv_size() };
                    const uint64_t name_hash { Utils::FNV1a<char>::hash(name.c_str(),
                                                                        name.size()) };
                    if (const auto lookup { satd.find(name_hash) }; lookup != satd.end()) {
                        return Create::symbol<Expression::BV>(
                            std::move(name), bl, Expression::Base::SPAV { lookup->second });
                    }
                    return Create::symbol<Expression::BV>(std::move(name), bl);
                }
                case Z3_BOOL_SORT:
                    return Create::symbol(std::move(name));
                case Z3_FLOATING_POINT_SORT: {
                    const auto width { z3_sort_to_fp_width(sort) };
                    if (LIKELY(width == Mode::FP::dbl)) {
                        return Create::symbol<Expression::FP>(std::move(name),
                                                              Mode::FP::dbl.width());
                    }
                    if (LIKELY(width == Mode::FP::flt)) {
                        return Create::symbol<Expression::FP>(std::move(name),
                                                              Mode::FP::flt.width());
                    }
                    throw Error::Backend::Unsupported(
                        WHOAMI_WITH_SOURCE REFUSE_FP_STANDARD "\nWidth: ", width);
                }
                default:
                    throw Error::Backend::Abstraction(
                        WHOAMI_WITH_SOURCE "Unknown sort_kind: ", sort.sort_kind(),
                        "\nOp decl: ", decl, "\nPlease report this.");
            }
        }
        // Unknown error
        else {
            const auto &ctx { Private::tl_ctx };
            throw Error::Backend::Abstraction(
                WHOAMI_WITH_SOURCE "Uninterpreted z3 op with args given. Op name: ",
                Z3_get_symbol_string(ctx, Z3_get_decl_name(ctx, decl)), "\nPlease report this.");
        }
    }

    /** A boolean expression
     *  Warning: Should not be inline b/c of ODR rules
     */
    template <bool B> const auto bool_ { Create::literal(B) };

    /** Abstraction function ofr various Z3 comparison ops */
    template <typename T, Mode::Compare Mask>
    inline Expression::BasePtr compare(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        return Create::compare<T, Mask>(GET_EARG(0), GET_EARG(1));
    }

    /**********************************************************/
    /*                        Logical                         */
    /**********************************************************/

    /** Abstraction function for z3 equality ops
     *  Will warn the user if called on Expression::FP while T is not that.
     */
    template <typename T = Expression::Base> inline Expression::BasePtr eq(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        if constexpr (std::is_same_v<T, Expression::FP>) {
            return Create::eq<T>(GET_EARG(0), GET_EARG(1));
        }
        if constexpr (std::is_same_v<T, Expression::Bool>) {
            return Create::eq<T>(GET_EARG(0), GET_EARG(1));
        }
        switch (GET_EARG(0)->cuid) {
            TYPE_CASE(Bool, Create::eq, GET_EARG(0), GET_EARG(1));
            TYPE_CASE(BV, Create::eq, GET_EARG(0), GET_EARG(1));
            TYPE_CASE(String, Create::eq, GET_EARG(0), GET_EARG(1));
            DEFAULT_TYPE_CASE(GET_EARG(0)->cuid);
            // This case should never be hit if used correctly
            // We can recover, but we will warn the user!
            case Expression::FP::static_cuid: {
                Utils::Log::warning(WHOAMI_WITH_SOURCE,
                                    "called on FP but without setting T to Ex::FP as expected."
                                    "\nIf you see this, please report it or correct your usage"
                                    " if you are using this function directly.");
                return Create::eq<Expression::FP>(GET_EARG(0), GET_EARG(1));
            }
        };
    }

    /** Abstraction function for Z3_OP_DISTINCT */
    inline Expression::BasePtr distinct(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        switch (GET_EARG(0)->cuid) {
            TYPE_CASE(FP, Create::neq, GET_EARG(0), GET_EARG(1));
            TYPE_CASE(Bool, Create::neq, GET_EARG(0), GET_EARG(1));
            DEFAULT_TYPE_CASE(GET_EARG(0)->cuid);
        };
    }

    /** Abstraction function for Z3_OP_ITE */
    inline Expression::BasePtr ite(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 3);
        switch (GET_EARG(1)->cuid) {
            TYPE_CASE(Bool, Create::if_, GET_EARG(0), GET_EARG(1), GET_EARG(2));
            TYPE_CASE(String, Create::if_, GET_EARG(0), GET_EARG(1), GET_EARG(2));
            TYPE_CASE(BV, Create::if_, GET_EARG(0), GET_EARG(1), GET_EARG(2));
            TYPE_CASE(FP, Create::if_, GET_EARG(0), GET_EARG(1), GET_EARG(2));
            TYPE_CASE(VS, Create::if_, GET_EARG(0), GET_EARG(1), GET_EARG(2));
            DEFAULT_TYPE_CASE(GET_EARG(1)->cuid);
        };
    }

    /** Abstraction function for z3 and ops */
    template <typename T> inline Expression::BasePtr and_(ArgsVec &args) {
        FLAT_BINARY(Create::and_<T>);
    }

    /** Abstraction function for z3 or ops */
    template <typename T> inline Expression::BasePtr or_(const ArgsVec &args) {
        FLAT_BINARY(Create::or_<T>);
    }

    /** Abstraction function for z3 xor ops */
    template <typename T> inline Expression::BasePtr xor_(const ArgsVec &args) {
        FLAT_BINARY(Create::xor_);
    }

    /** Abstraction function for z3 not/inversion ops */
    template <typename T> inline Expression::BasePtr not_(const ArgsVec &args) {
        if constexpr (std::is_same_v<T, Expression::Bool>) {
            UNARY(Create::not_);
        }
        else if constexpr (std::is_same_v<T, Expression::BV>) {
            UNARY(Create::invert);
        }
    }

    /**********************************************************/
    /*                       Arithmetic                       */
    /**********************************************************/

    /** Abstraction function for z3 negation ops */
    template <typename T> inline Expression::BasePtr neg(const ArgsVec &args) {
        UNARY(Create::neg<T>);
    }

    /** Abstraction function for Z3_OP_BADD */
    inline Expression::BasePtr abs(const ArgsVec &args) { UNARY(Create::abs) }

    /** Abstraction function for Z3_OP_BADD */
    inline Expression::BasePtr add(const ArgsVec &args) { FLAT_BINARY(Create::add); }

    /** Abstraction function for Z3_OP_BSUB */
    inline Expression::BasePtr sub(const ArgsVec &args) { BINARY(Create::sub); }

    /** Abstraction function for Z3_OP_BMUL */
    inline Expression::BasePtr mul(const ArgsVec &args) { FLAT_BINARY(Create::mul); }

    /** Abstraction function for z3 BV division */
    template <bool Signed> inline Expression::BasePtr div(const ArgsVec &args) {
        BINARY(Create::div<Signed>);
    }

    /** Abstraction function for z3 BV remainder
     *  Note we use mod (because of the difference between C and Python % operators)
     */
    template <bool Signed> inline Expression::BasePtr rem(const ArgsVec &args) {
        BINARY(Create::mod<Signed>);
    }

    /**********************************************************/
    /*                       Bit Vector                       */
    /**********************************************************/

    namespace BV {

        /** The primitive variant BV functions use */
        using PrimVar = std::variant<uint8_t, uint16_t, uint32_t, uint64_t, BigInt>;

        /** Abstraction function for Z3_OP_BNUM to a primitive */
        inline PrimVar num_primtive(const z3::expr &b_obj) {
            using Err = Utils::Error::Unexpected::Type;
            const auto bl { b_obj.get_sort().bv_size() };

            // Standard sizes
            if (bl <= 64) {
                uint64_t u64;
                Utils::affirm<Err>(b_obj.is_numeral_u64(u64),
                                   WHOAMI_WITH_SOURCE "given z3 object is not a numeral");
                switch (bl) {
                    case 8:
                        return Utils::narrow<uint8_t>(u64);
                    case 16:
                        return Utils::narrow<uint16_t>(u64);
                    case 32:
                        return Utils::narrow<uint32_t>(u64);
                    case 64:
                        return u64;
                    default:
                        break;
                };
            }

            // Get the BV as a BigInt
            std::string str;
            Utils::affirm<Err>(b_obj.is_numeral(str),
                               WHOAMI_WITH_SOURCE "given z3 object is not a numeral");
            return BigInt { BigInt::Value { str }, bl };
        }

        /** Abstraction function for Z3_OP_BNUM */
        inline Expression::BasePtr num(const z3::expr &b_obj) {
            PrimVar x { num_primtive(b_obj) }; // Not const for move purposes
                                               /** A local helper macro */
#define G_CASE(I)                                                                                 \
    case I:                                                                                       \
        return Create::literal(std::get<I>(x));
            switch (x.index()) {
                G_CASE(0)
                G_CASE(1)
                G_CASE(2)
                G_CASE(3)
                case 4:
                    UTILS_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(x, 4, BigInt);
                    return Create::literal(std::move(std::get<BigInt>(x)));
                default:
                    throw Utils::Error::Unexpected::Unknown(WHOAMI_WITH_SOURCE, "Bad variant");
            }
#undef G_CASE
            static_assert(std::variant_size_v<PrimVar> == 5,
                          "Switch-case statement needs to be modified");
        }

    } // namespace BV

    // BV Bitwise

    /** Abstraction function for BV shifts */
    template <Mode::Shift Mask> inline Expression::BasePtr shift(const ArgsVec &args) {
        BINARY(Create::shift<Mask>);
    }

    /** Abstraction function for BV rotations */
    template <Mode::LR LR> inline Expression::BasePtr rotate(const ArgsVec &args) {
        BINARY(Create::rotate<LR>);
    }

    // BV Misc

    /** Abstraction function for Z3_OP_CONCAT */
    inline Expression::BasePtr concat(const ArgsVec &args) {
        BINARY(Create::concat<Expression::BV>);
    }

    /** Abstraction function for Z3_OP_SIGN_EXT */
    inline Expression::BasePtr sign_ext(const ArgsVec &args, const z3::func_decl &decl) {
        UINT_BINARY(Create::sign_ext);
    }

    /** Abstraction function for Z3_OP_ZERO_EXT */
    inline Expression::BasePtr zero_ext(const ArgsVec &args, const z3::func_decl &decl) {
        UINT_BINARY(Create::zero_ext);
    }

    /** Abstraction function for Z3_OP_EXTRACT */
    inline Expression::BasePtr extract(const ArgsVec &args, const z3::expr &e) {
        ASSERT_ARG_LEN(args, 1);
        return Create::extract(e.hi(), e.lo(), GET_EARG(0));
    }

    /**********************************************************/
    /*                     Floating Point                     */
    /**********************************************************/

    namespace FP {

        // Conversions

        /** Abstraction function for Z3_OP_FPA_TO_SBV and Z3_OP_FPA_TO_UBV */
        template <bool Signed>
        inline Expression::BasePtr to_bv(const ArgsVec &args, const z3::func_decl &decl) {
            ASSERT_ARG_LEN(args, 2);
            return Create::FP::to_bv<Signed>(
                std::get<Mode::FP::Rounding>(args[0]), GET_EARG(1),
                static_cast<Constants::UInt>(Z3_get_decl_int_parameter(Private::tl_ctx, decl, 0)));
        }

        /** Abstraction function for Z3_OP_FPA_TO_IEEE_BV */
        inline Expression::BasePtr to_ieee_bv(const ArgsVec &args) {
            UNARY(Create::FP::to_ieee_bv);
        }

        /** Abstraction function for Z3_OP_FPA_TO_IEEE_BV
         *  TODO
         */
        inline Expression::BasePtr to_fp(const ArgsVec &args) {
            (void) args;
            throw Utils::Error::Unexpected::Base("This is not yet supported");
        }

        /** Abstraction function for Z3_OP_FPA_NUM to a primtive type
         *  Note: this function can only handle 32 bit and 64 bit floats
         */
        inline std::variant<double, float> num_primitive(const z3::expr &b_obj) {
            const auto &ctx { Private::tl_ctx };

            // To extend this function to handle bigger floats, we need to use these functions:
            //   z3.Z3_fpa_get_numeral_significand_string (has the leading 1. or 0.)
            //   z3.Z3_fpa_get_numeral_exponent_string

            // Fp components
            int sign;          // NOLINT
            uint64_t mantissa; // NOLINT
            int64_t exp;       // NOLINT

            // Extract fp components (success is false if the size is too large)
            bool success { Z3_fpa_get_numeral_sign(ctx, b_obj, &sign) };
            success &= Z3_fpa_get_numeral_significand_uint64(ctx, b_obj, &mantissa);
            success &= Z3_fpa_get_numeral_exponent_int64(ctx, b_obj, &exp, true);

            // Error check
            Utils::affirm<Utils::Error::Unexpected::Unknown>(
                success,
                WHOAMI_WITH_SOURCE
                "something went wrong with fp component extraction.\nGiven fp: ",
                b_obj);

            const auto sort { b_obj.get_sort() };
            const auto width { z3_sort_to_fp_width(sort) };
            namespace FP = Mode::FP;
            if (LIKELY(width == FP::dbl)) {
                const uint64_t to_val {
                    (Utils::widen<uint64_t, true>(sign) << FP::dbl.no_sign_width()) | mantissa |
                    (Utils::unsign(exp) << FP::dbl.mantissa_raw())
                };
                // If nothing went wrong, this reinterpret_cast should be safe
                return *reinterpret_cast<const double *>(&to_val);
            }
            if (LIKELY(width == FP::flt)) {
                const uint32_t to_val { (Utils::unsign(sign) << FP::flt.no_sign_width()) |
                                        Utils::narrow<uint32_t>(mantissa) |
                                        (Utils::narrow<uint32_t, true>(exp)
                                         << FP::flt.mantissa_raw()) };
                // If nothing went wrong, this reinterpret_cast should be safe
                return *reinterpret_cast<const float *>(&to_val);
            }
            throw Utils::Error::Unexpected::NotSupported(
                WHOAMI_WITH_SOURCE
                "Cannot create a value for this unknown floating point standard."
                "\nZ3_sort: ",
                sort);
        }

        /** Abstraction function for Z3_OP_FPA_NUM */
        inline Expression::BasePtr num(const z3::expr &b_obj) {
            const std::variant<double, float> x { num_primitive((b_obj)) };
            if (LIKELY(x.index() == 0)) {
                return Create::literal(std::get<double>(x));
            }
            return Create::literal(std::get<float>(x));
        }

        // Constants

        namespace Private {

            /** std::copysign if Real is signed, else return x */
            template <Mode::Sign::Real Sign, typename T> constexpr T copysign(const T x) {
                if constexpr (Sign != Mode::Sign::Real::None) {
                    return std::copysign(x, T { Utils::to_underlying(Sign) });
                }
                return x;
            }

            /** A helper function to assist in creating FPA literals */
            template <Mode::Sign::Real Sign>
            inline Expression::BasePtr fpa_literal(const z3::expr &b_obj, const double dbl,
                                                   const float flt) {
                const auto sort { b_obj.get_sort() };
                const auto width { z3_sort_to_fp_width(sort) };
                if (LIKELY(width == Mode::FP::dbl)) {
                    return Create::literal(copysign<Sign>(dbl));
                }
                if (LIKELY(width == Mode::FP::flt)) {
                    return Create::literal(copysign<Sign>(flt));
                }
                throw Error::Backend::Unsupported(WHOAMI_WITH_SOURCE REFUSE_FP_STANDARD "\nSort: ",
                                                  sort);
            }

            /** A helper function to assist in creating FPA literals
             *  A specialization which use a Mode::Sign::FP
             */
            template <Mode::Sign::FP Sign, typename... Args>
            inline auto fpa_literal(Args &&...args) {
                return fpa_literal<Mode::Sign::to_real(Sign)>(std::forward<Args>(args)...);
            }

        } // namespace Private

        /** Abstraction function for fpa zeros */
        template <Mode::Sign::FP Sign> inline Expression::BasePtr zero(const z3::expr &b_obj) {
            return Private::fpa_literal<Sign>(b_obj, 0., 0.F);
        }

        /** Abstraction function for fpa inf */
        template <Mode::Sign::FP Sign> inline Expression::BasePtr inf(const z3::expr &b_obj) {
            static_assert(std::numeric_limits<double>::is_iec559, "IEE 754 required for -inf");
            static_assert(std::numeric_limits<float>::is_iec559, "IEE 754 required for -inf");
            static const constexpr float inf_f { std::numeric_limits<float>::infinity() };
            static const constexpr double inf_d { std::numeric_limits<double>::infinity() };
            return Private::fpa_literal<Sign>(b_obj, inf_d, inf_f);
        }

        /** Abstraction function for Z3_OP_FPA_NAN
         *  Note: SMT theory of floating point numbers only has one NaN, it does not
         *  distinguish between quiet and signalling NaNs.
         *  We choose quiet as the type of nan we return
         */
        inline Expression::BasePtr nan(const z3::expr &b_obj) {
            namespace Z = ::Backend::Z3;
            return Private::fpa_literal<Mode::Sign::Real::None>(b_obj, Z::nan<double>,
                                                                Z::nan<float>);
        }

        // Comparisons

        // Arithmetic

        /** Abstraction function for Z3_OP_FPA_ADD */
        inline Expression::BasePtr add(const ArgsVec &args) { MODE_BINARY(Create::FP::add); }

        /** Abstraction function for Z3_OP_FPA_SUB */
        inline Expression::BasePtr sub(const ArgsVec &args) { MODE_BINARY(Create::FP::sub); }

        /** Abstraction function for Z3_OP_FPA_MUL */
        inline Expression::BasePtr mul(const ArgsVec &args) { MODE_BINARY(Create::FP::mul); }

        /** Abstraction function for Z3_OP_FPA_DIV */
        inline Expression::BasePtr div(const ArgsVec &args) { MODE_BINARY(Create::FP::div); }

    } // namespace FP

// Cleanup
#undef DEFAULT_TYPE_CASE
#undef ASSERT_ARG_LEN
#undef TYPE_CASE
#undef FLAT_BINARY
#undef MODE_BINARY
#undef UINT_BINARY
#undef BINARY
#undef UNARY

} // namespace Backend::Z3::Abstract

#endif
