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
#include "../abstraction_variant.hpp"

#include <cmath>
#include <limits>


namespace Backend::Z3::Abstract {

    /** The 'args' array type */
    using ArgsVec = std::vector<::Backend::Private::AbstractionVariant>;

/** A local macro used for lengh checking the number of children in a container */
#define ASSERT_ARG_LEN(X, N)                                                                      \
    Utils::affirm<Utils::Error::Unexpected::Size>((X).size() == (N), WHOAMI_WITH_SOURCE "Op ",    \
                                                  __func__, " should have " #N " children.");

/** A local macro used for adding a case for a given type
 *  Func must be take in T as its only template argument
 */
#define TYPE_CASE(TYPE, FUNC, ...)                                                                \
    case Expression::TYPE::static_cuid:                                                           \
        return FUNC<Expression::TYPE>(__VA_ARGS__);

/** A local macro used for adding a case for a given type
 *  Func must take in <TYPE, T2> as its template arguments
 */
#define TYPE_CASE_2(TYPE, T2, FUNC, ...)                                                          \
    case Expression::TYPE::static_cuid:                                                           \
        return FUNC<Expression::TYPE, T2>(__VA_ARGS__);

/** A local macro used for adding a default type case that throws an exception */
#define DEFAULT_TYPE_CASE(BAD_CUID)                                                               \
    default:                                                                                      \
        throw Utils::Error::Unexpected::Type(WHOAMI_WITH_SOURCE,                                  \
                                             "Unexpected type detected. CUID: ", (BAD_CUID));

/** A local macro for getting the X'th element of 'args' as an expression */
#define GET_EARG(I) std::get<Expression::BasePtr>(args[(I)])

    /**********************************************************/
    /*                        General                         */
    /**********************************************************/

    /** Abstraction function for Z3_OP_UNINTERPRETED */
    inline Expression::BasePtr uninterpreted(const z3::func_decl &decl,
                                             const Z3_decl_kind decl_kind, const z3::sort &sort,
                                             const ArgsVec &args) {
        // If b_obj is a symbolic value
        if (args.empty()) {
            // Gather info
            std::string name { decl.name().str() };
            auto symbol_type { sort.sort_kind() };
            switch (symbol_type) {
                case Z3_BV_SORT:
                    /* const auto bl { sort.bv_size() }; */
                    /* bv_size = z3.Z3_get_bv_sort_size(ctx, z3_sort) */
                    /* (ast_args, annots) = self.extra_bvs_data.get(symbol_name, (None,
                     * None)) */
                    /* if ast_args is None: */
                    /*     ast_args = (symbol_str, None, None, None, False, False,
                     * None) */
                    /* return Create::symbol(std::move(name), bl, ans); // probably?
                     * TODO: */
                    return nullptr;
                case Z3_BOOL_SORT:
                case Z3_FLOATING_POINT_SORT:
                default:
                    throw Error::Backend::Abstraction(
                        WHOAMI_WITH_SOURCE "Unknown term type: ", symbol_type,
                        "\nOp decl_kind: ", decl_kind, "\nPlease report this.");
            }
        }
        // Unknown error
        else {
            throw Error::Backend::Abstraction(
                WHOAMI_WITH_SOURCE "Uninterpreted z3 op with args given. Op decl_kind: ",
                decl_kind, "\nPlease report this.");
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
        return Create::neq<Expression::Bool>(GET_EARG(0), GET_EARG(1));
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
        ASSERT_ARG_LEN(args, 2);
        return Create::and_<T>({ std::move(GET_EARG(0)), std::move(GET_EARG(1)) });
    }

    /** Abstraction function for z3 or ops */
    template <typename T> inline Expression::BasePtr or_(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        return Create::or_<T>({ std::move(GET_EARG(0)), std::move(GET_EARG(1)) });
    }

    /** Abstraction function for z3 xor ops */
    template <typename T> inline Expression::BasePtr xor_(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        return Create::xor_({ std::move(GET_EARG(0)), std::move(GET_EARG(1)) });
    }

    /** Abstraction function for invert z3 ops */
    template <typename T> inline Expression::BasePtr not_(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 1);
        return Create::invert<T>(GET_EARG(0));
    }

    /**********************************************************/
    /*                       Arithmetic                       */
    /**********************************************************/

    /** Abstraction function for z3 negation ops */
    template <typename T> inline Expression::BasePtr neg(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 1);
        return Create::neg<T>(GET_EARG(0));
    }

    /** Abstraction function for Z3_OP_BADD */
    template <typename T> inline Expression::BasePtr abs(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 1);
        return Create::abs<T>(GET_EARG(0));
    }

    /** Abstraction function for Z3_OP_BADD */
    inline Expression::BasePtr add(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        return Create::add({ std::move(GET_EARG(0)), std::move(GET_EARG(1)) });
    }

    /** Abstraction function for Z3_OP_BSUB */
    inline Expression::BasePtr sub(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        return Create::sub(GET_EARG(0), GET_EARG(1));
    }

    /** Abstraction function for Z3_OP_BMUL */
    inline Expression::BasePtr mul(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        return Create::mul({ std::move(GET_EARG(0)), std::move(GET_EARG(1)) });
    }

    /** Abstraction function for z3 BV division */
    template <bool Signed> inline Expression::BasePtr div(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        return Create::div<Signed>(GET_EARG(0), GET_EARG(1));
    }

    /** Abstraction function for z3 BV remainder
     *  Note we use mod (because of the difference between C and Python % operators)
     */
    template <bool Signed> inline Expression::BasePtr rem(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        return Create::mod<Signed>(GET_EARG(0), GET_EARG(1));
    }

    /** Abstraction function for Z3_OP_POWER */
    inline Expression::BasePtr pow(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        return Create::pow(GET_EARG(0), GET_EARG(1));
    }

    /**********************************************************/
    /*                       Bit Vector                       */
    /**********************************************************/

    namespace BV {

        /** Abstraction function for Z3_OP_BNUM */
        inline Expression::BasePtr num(Constants::CTSC<z3::expr> b_obj, const z3::sort &sort) {
            // Get the bv number
            uint64_t bv_num; // NOLINT
            if (!b_obj->is_numeral_u64(bv_num)) {
                std::string tmp;
                const bool success { b_obj->is_numeral(tmp) };
                Utils::affirm<Utils::Error::Unexpected::Type>(success, WHOAMI_WITH_SOURCE
                                                              "given z3 object is not a numeral");
                bv_num = std::stoull(tmp); // Faster than istringstream
                static_assert(sizeof(unsigned long long) == sizeof(uint64_t),
                              "Bad string conversion function called");
            }
            // Type pun to vector of bytes
            std::vector<std::byte> data;
            data.reserve(sizeof(bv_num));
            std::memcpy(data.data(), &bv_num, sizeof(bv_num));
            // Size check
            const auto bl { sort.bv_size() };
            Utils::affirm<Utils::Error::Unexpected::Size>(
                sizeof(bv_num) == bl * 8,
                WHOAMI_WITH_SOURCE "Int to BV type pun failed because the requested BV size"
                                   "size is ",
                bl, " bits long where as the integer type is only ", sizeof(bv_num) * 8,
                "bytes long.");
            // Return literal
            return Create::literal(std::move(data));
        }

    } // namespace BV

    /** Abstraction function for Z3_OP_CONCAT */
    inline Expression::BasePtr concat(const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 2);
        return Create::concat<Expression::BV>(GET_EARG(0), GET_EARG(1));
    }

    /** Abstraction function for Z3_OP_SIGN_EXT */
    inline Expression::BasePtr sign_ext(const z3::func_decl &decl, const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 1);
        const auto val { static_cast<z3u>(
            Z3_get_decl_int_parameter(Private::tl_raw_ctx, decl, 0)) };
        return Create::sign_ext(GET_EARG(0), Utils::widen<Constants::UInt>(val));
    }

    /** Abstraction function for Z3_OP_ZERO_EXT */
    inline Expression::BasePtr zero_ext(const z3::func_decl &decl, const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 1);
        const auto val { static_cast<z3u>(
            Z3_get_decl_int_parameter(Private::tl_raw_ctx, decl, 0)) };
        return Create::sign_ext(GET_EARG(0), Utils::widen<Constants::UInt>(val));
    }

    /** Abstraction function for Z3_OP_EXTRACT */
    inline Expression::BasePtr extract(Constants::CTSC<z3::expr> b_obj, const ArgsVec &args) {
        ASSERT_ARG_LEN(args, 1);
        return Create::extract(b_obj->hi(), b_obj->lo(), GET_EARG(0));
    }

    /**********************************************************/
    /*                     Floating Point                     */
    /**********************************************************/

    namespace FP {

        // Conversions

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
            inline Expression::BasePtr fpa_literal(const Z3_sort_kind sort_kind, const double dbl,
                                                   const float flt) {
                if (LIKELY(sort_kind == ::Backend::Z3::Private::z3_dbl)) {
                    return Create::literal(copysign<Sign>(dbl));
                }
                if (LIKELY(sort_kind == ::Backend::Z3::Private::z3_flt)) {
                    return Create::literal(copysign<Sign>(flt));
                }
                throw Utils::Error::Unexpected::NotSupported(
                    WHOAMI_WITH_SOURCE
                    "Cannot create a zero value for this unknown floating point standard."
                    "\nZ3_sort_kind: ",
                    sort_kind);
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
        template <Mode::Sign::FP Sign>
        inline Expression::BasePtr zero(const Z3_sort_kind sort_kind) {
            return Private::fpa_literal<Sign>(sort_kind, 0., 0.f);
        }

        /** Abstraction function for fpa inf */
        template <Mode::Sign::FP Sign>
        inline Expression::BasePtr inf(const Z3_sort_kind sort_kind) {
            static_assert(std::numeric_limits<double>::is_iec559, "IEE 754 required for -inf");
            static_assert(std::numeric_limits<float>::is_iec559, "IEE 754 required for -inf");
            static const constexpr float inf_f { std::numeric_limits<float>::infinity() };
            static const constexpr double inf_d { std::numeric_limits<double>::infinity() };
            return Private::fpa_literal<Sign>(sort_kind, inf_d, inf_f);
        }

        /** Abstraction function for Z3_OP_FPA_NAN
         *  TODO: determine if it should be quiet or signalling
         */
        inline Expression::BasePtr nan(const Z3_sort_kind sort_kind) {
            static_assert(std::numeric_limits<float>::has_quiet_NaN, "Unable to generate NaN");
            static_assert(std::numeric_limits<double>::has_quiet_NaN, "Unable to generate NaN");
            static const constexpr float nan_f { std::numeric_limits<float>::quiet_NaN() };
            static const constexpr double nan_d { std::numeric_limits<double>::quiet_NaN() };
            return Private::fpa_literal<Mode::Sign::Real::None>(sort_kind, nan_d, nan_f);
        }

        // Comparisons

        // Arithmetic

        /** Abstraction function for Z3_OP_FPA_ADD */
        inline Expression::BasePtr add(const ArgsVec &args) {
            ASSERT_ARG_LEN(args, 2);
            return Create::FP::add(GET_EARG(1), GET_EARG(2),
                                   std::get<Mode::FP::Rounding>(args[0]));
        }

        /** Abstraction function for Z3_OP_FPA_SUB */
        inline Expression::BasePtr sub(const ArgsVec &args) {
            ASSERT_ARG_LEN(args, 2);
            return Create::FP::sub(GET_EARG(1), GET_EARG(2),
                                   std::get<Mode::FP::Rounding>(args[0]));
        }

        /** Abstraction function for Z3_OP_FPA_MUL */
        inline Expression::BasePtr mul(const ArgsVec &args) {
            ASSERT_ARG_LEN(args, 2);
            return Create::FP::mul(GET_EARG(1), GET_EARG(2),
                                   std::get<Mode::FP::Rounding>(args[0]));
        }

        /** Abstraction function for Z3_OP_FPA_DIV */
        inline Expression::BasePtr div(const ArgsVec &args) {
            ASSERT_ARG_LEN(args, 2);
            return Create::FP::div(GET_EARG(1), GET_EARG(2),
                                   std::get<Mode::FP::Rounding>(args[0]));
        }

    } // namespace FP

// Cleanup
#undef DEFAULT_TYPE_CASE
#undef ASSERT_ARG_LEN
#undef TYPE_CASE_2
#undef TYPE_CASE

} // namespace Backend::Z3::Abstract

#endif
