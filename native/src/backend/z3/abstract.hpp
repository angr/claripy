/**
 * @file
 * @brief This file defines how the Z3 backend converts Z3 ASTs into Claricpp Exprs
 */
#ifndef R_SRC_BACKEND_Z3_ABSTRACT_HPP_
#define R_SRC_BACKEND_Z3_ABSTRACT_HPP_

#include "constants.hpp"
#include "width_translation.hpp"

#include "../../create.hpp"

#include <cmath>
#include <limits>


#define M_ASSERT_ARG_LEN(X, N)                                                                     \
    UTIL_ASSERT(Util::Err::Size, (X).size() == (N),                                                \
                "Op should have " #N " children, but instead has: ", (X).size());

#define M_REFUSE_FP_STANDARD                                                                       \
    "Refusing to use unknown point standard as the rules about bit manipulation on this "          \
    "standard may differ from expected."

#define M_GET_EARG(I) std::get<Expr::BasePtr>(args[(I)])

// Macros for each op category
// Assumes the arguments array is called args
// FUNC may *not* have commas in it

#define M_UNARY(FUNC)                                                                              \
    M_ASSERT_ARG_LEN(args, 1);                                                                     \
    return FUNC(M_GET_EARG(0));

// Assumes decl is called decl
#define M_UINT_BINARY(FUNC)                                                                        \
    M_ASSERT_ARG_LEN(args, 1);                                                                     \
    return FUNC(M_GET_EARG(0), Util::widen<U64, true>(Z3_get_decl_int_parameter(ctx, decl, 0)));

#define M_BINARY(FUNC)                                                                             \
    M_ASSERT_ARG_LEN(args, 2);                                                                     \
    return FUNC(M_GET_EARG(0), M_GET_EARG(1), { nullptr });

#define M_MODEBINARY(FUNC)                                                                         \
    M_ASSERT_ARG_LEN(args, 3);                                                                     \
    return FUNC(M_GET_EARG(1), M_GET_EARG(2), std::get<Mode::FP::Rounding>(args[0]));

#define M_FLAT_BINARY(FUNC)                                                                        \
    M_ASSERT_ARG_LEN(args, 2);                                                                     \
    return FUNC({ std::move(M_GET_EARG(0)), std::move(M_GET_EARG(1)) });


namespace Backend::Z3 {

    /** The abstraction class */
    /** Used to convert Z3 ASTs exprs into Claricpp exprs */
    template <typename Z3> struct Abstract final {
        static_assert(typename Z3::IsZ3Bk(), "Z3 should be the Z3 backend");

        /** The 'args' array type */
        using ArgsVec = std::vector<typename Z3::AbstractionVariant>;

        /**********************************************************/
        /*                        General                         */
        /**********************************************************/

        /** Abstraction function for Z3_OP_INTERNAL to a primitive */
        static CCSC internal_primitive(const z3::expr &b, const z3::func_decl &decl) {
#if 1
            const auto &ctx { b.ctx() };
            if (UNLIKELY((Z3_get_decl_num_parameters(ctx, decl) != 1) ||
                         (Z3_get_decl_parameter_kind(ctx, decl, 0) != Z3_PARAMETER_SYMBOL))) {
                UTIL_THROW(Error::Backend::Abstraction, "Weird Z3 model (Type 1).", b);
            }
            const auto symb { Z3_get_decl_symbol_parameter(ctx, decl, 0) };
            if (UNLIKELY(Z3_get_symbol_kind(ctx, symb) != Z3_STRING_SYMBOL)) {
                UTIL_THROW(Error::Backend::Abstraction, "Weird Z3 model (Type 2).", b);
            }
            Util::Log::error(WHOAMI "String literal abstraction is incomplete.");
            return Z3_get_symbol_string(ctx, symb);
                // TODO: return z3_str.encode("utf-8").decode("unicode_escape")
#else
            // TODO: Check if this is better
            // Return e.get_string().encode('utf-8').decode('unicode_escape')
            std::wstring_convert < std::codecvt<utf8<char32_t>, char32_t> conv;
            return conv.to_bytes(b.get_u32string());
#endif
        }

        /** Abstraction function for Z3_OP_INTERNAL */
        static Expr::BasePtr internal(const z3::expr &b, const z3::func_decl &decl) {
            return Create::literal(std::string { internal_primitive(b, decl) });
        }

        /** Abstraction function for Z3_OP_UNINTERPRETED */
        static Expr::BasePtr uninterpreted(const z3::expr &b_obj, const z3::func_decl &decl,
                                           const ArgsVec &args, SymAnTransData &satd) {
            const auto sort { b_obj.get_sort() };
            // If b_obj is a symbolic value
            if (LIKELY(args.empty())) {
                // Gather info
                std::string name { decl.name().str() };
                switch (sort.sort_kind()) {
                    case Z3_BV_SORT: {
                        const auto bl { sort.bv_size() };
                        const U64 name_hash { Util::FNV1a<char>::hash(name.c_str(), name.size()) };
                        if (const auto lookup { satd.find(name_hash) }; lookup != satd.end()) {
                            return Create::symbol<Expr::BV>(std::move(name), bl,
                                                            Annotation::SPAV { lookup->second });
                        }
                        return Create::symbol_bv(std::move(name), bl);
                    }
                    case Z3_BOOL_SORT:
                        return Create::symbol_bool(std::move(name));
                    case Z3_FLOATING_POINT_SORT: {
                        const auto width { z3_sort_to_fp_width(sort) };
                        if (LIKELY(width == Mode::FP::dbl)) {
                            return Create::symbol_fp(std::move(name), Mode::FP::dbl.width());
                        }
                        if (LIKELY(width == Mode::FP::flt)) {
                            return Create::symbol_fp(std::move(name), Mode::FP::flt.width());
                        }
                        UTIL_THROW(Error::Backend::Unsupported,
                                   M_REFUSE_FP_STANDARD "\nWidth: ", width);
                    }
                    default:
                        UTIL_THROW(Error::Backend::Abstraction,
                                   "Unknown sort_kind: ", sort.sort_kind(), "\nOp decl: ", decl,
                                   "\nPlease report this.");
                }
            }
            // Unknown error
            else {
                auto &ctx { decl.ctx() };
                UTIL_THROW(Error::Backend::Abstraction,
                           "Uninterpreted z3 op with args given. Op name: ",
                           Z3_get_symbol_string(ctx, Z3_get_decl_name(ctx, decl)),
                           "\nPlease report this.");
            }
        }

        /** A boolean expr */
        template <bool B> static Expr::BasePtr bool_() {
            static Expr::BasePtr ret { nullptr };
            if (UNLIKELY(ret == nullptr)) {
                ret = Create::literal(B);
            }
            return ret;
        }

        /** Abstraction function for various Z3 comparison ops */
        template <typename OpT> static Expr::BasePtr inequality(const ArgsVec &args) {
            static_assert(std::is_base_of_v<Op::Inequality, OpT>, "Op must derive from inequality");
            M_ASSERT_ARG_LEN(args, 2);
            return Create::inequality<OpT>(M_GET_EARG(0), M_GET_EARG(1), { nullptr });
        }

        /**********************************************************/
        /*                        Logical                         */
        /**********************************************************/

        /** Abstraction function for z3 equality ops
         *  Will warn the user if called on Expr::FP while T is not that.
         */
        static Expr::BasePtr eq(const ArgsVec &args) {
            M_ASSERT_ARG_LEN(args, 2);
            return Create::eq(M_GET_EARG(0), M_GET_EARG(1));
        }

        /** Abstraction function for Z3_OP_DISTINCT */
        static Expr::BasePtr distinct(const ArgsVec &args) {
            M_ASSERT_ARG_LEN(args, 2);
            return Create::neq(M_GET_EARG(0), M_GET_EARG(1));
        }

        /** Abstraction function for Z3_OP_ITE */
        static Expr::BasePtr ite(const ArgsVec &args) {
            M_ASSERT_ARG_LEN(args, 3);
            return Create::if_(M_GET_EARG(0), M_GET_EARG(1), M_GET_EARG(2));
        }

        /** Abstraction function for z3 and ops */
        static Expr::BasePtr and_(ArgsVec &args) {
            M_FLAT_BINARY(Create::and_);
        }

        /** Abstraction function for z3 or ops */
        static Expr::BasePtr or_(const ArgsVec &args) {
            M_FLAT_BINARY(Create::or_);
        }

        /** Abstraction function for z3 xor ops */
        static Expr::BasePtr xor_(const ArgsVec &args) {
            M_FLAT_BINARY(Create::xor_);
        }

        /** Abstraction function for z3 not/inversion ops */
        template <typename T> static Expr::BasePtr not_(const ArgsVec &args) {
            if constexpr (std::is_same_v<T, Expr::Bool>) {
                M_UNARY(Create::not_);
            }
            else if constexpr (std::is_same_v<T, Expr::BV>) {
                M_UNARY(Create::invert);
            }
        }

        /**********************************************************/
        /*                       Arithmetic                       */
        /**********************************************************/

        /** Abstraction function for z3 negation ops */
        static Expr::BasePtr neg(const ArgsVec &args) {
            M_UNARY(Create::neg);
        }

        /** Abstraction function for Z3_OP_BADD */
        static Expr::BasePtr abs(const ArgsVec &args) {
            M_UNARY(Create::abs)
        }

        /** Abstraction function for Z3_OP_BADD */
        static Expr::BasePtr add(const ArgsVec &args) {
            M_FLAT_BINARY(Create::add);
        }

        /** Abstraction function for Z3_OP_BSUB */
        static Expr::BasePtr sub(const ArgsVec &args) {
            M_BINARY(Create::sub);
        }

        /** Abstraction function for Z3_OP_BMUL */
        static Expr::BasePtr mul(const ArgsVec &args) {
            M_FLAT_BINARY(Create::mul);
        }

        /** Abstraction function for signed z3 BV division */
        static Expr::BasePtr div_signed(const ArgsVec &args) {
            M_BINARY(Create::div_signed);
        }

        /** Abstraction function for unsigned z3 BV division */
        static Expr::BasePtr div_unsigned(const ArgsVec &args) {
            M_BINARY(Create::div_unsigned);
        }

        /** Abstraction function for z3 BV remainder
         *  Note we use mod (because of the difference between C and Python % operators)
         */
        static Expr::BasePtr rem_signed(const ArgsVec &args) {
            M_BINARY(Create::mod_signed);
        }

        /** Abstraction function for z3 BV remainder
         *  Note we use mod (because of the difference between C and Python % operators)
         */
        static Expr::BasePtr rem_unsigned(const ArgsVec &args) {
            M_BINARY(Create::mod_unsigned);
        }

        /**********************************************************/
        /*                       Bit Vector                       */
        /**********************************************************/

        /** A struct meant for certain BV abstractions */
        struct BV final {

            /** The primitive variant BV functions use */
            using BVVar = Op::BVTL::Apply<std::variant>;

            /** Abstraction function for Z3_OP_BNUM to a primitive */
            static BVVar num_primtive(const z3::expr &b_obj) {
                using E = Util::Err::Type;
                const auto bl { b_obj.get_sort().bv_size() };

                // Standard sizes
                if (bl <= 64) {
                    uint64_t u64; // Not U64 b/c z3
                    UTIL_ASSERT(E, b_obj.is_numeral_u64(u64), "given z3 object is not a numeral");
                    switch (bl) {
                        case 8:
                            return Util::narrow<uint8_t>(u64);
                        case 16:
                            return Util::narrow<uint16_t>(u64);
                        case 32:
                            return Util::narrow<uint32_t>(u64);
                        case 64:
                            return static_cast<U64>(u64);
                        default:
                            break;
                    };
                }

                // Get the BV as a BigInt
                std::string str;
                UTIL_ASSERT(E, b_obj.is_numeral(str), "given z3 object is not a numeral");
                return BigInt::from_str(std::move(str), bl);
            }

            /** Abstraction function for Z3_OP_BNUM */
            static Expr::BasePtr num(const z3::expr &b_obj) {
                BVVar x { num_primtive(b_obj) }; // Not const for move purposes
#define M_G_CASE(TYPE)                                                                             \
    case Util::Type::index<BVVar, TYPE>:                                                           \
        return Create::literal(std::get<TYPE>(x));
                // Switch on the type of x
                switch (x.index()) {
                    M_G_CASE(uint8_t)
                    M_G_CASE(uint16_t)
                    M_G_CASE(uint32_t)
                    M_G_CASE(U64)
                    case Util::Type::index<BVVar, BigInt>:
                        return Create::literal(std::move(std::get<BigInt>(x)));
                    case Util::Type::index<BVVar, PyObj::BVVS::Ptr>:
                        UTIL_THROW(Util::Err::Unknown, "PyObj::BVVSs should not be here");
                    default:
                        UTIL_THROW(Util::Err::Unknown, "Bad variant");
                }
#undef M_G_CASE
                static_assert(std::variant_size_v<BVVar> == 6,
                              "Switch-case statement needs to be modified");
            }

        }; // namespace BV

        // BV Bitwise

        /** Abstraction function for BV shifts */
        template <typename OpT> static Expr::BasePtr shift(const ArgsVec &args) {
            M_BINARY(Create::shift<OpT>);
        }

        /** Abstraction function for BV left rotations */
        static Expr::BasePtr rotate_left(const ArgsVec &args) {
            M_BINARY(Create::rotate_left);
        }

        /** Abstraction function for BV right rotations */
        static Expr::BasePtr rotate_right(const ArgsVec &args) {
            M_BINARY(Create::rotate_right);
        }

        // BV Misc

        /** Abstraction function for Z3_OP_CONCAT */
        static Expr::BasePtr concat(const ArgsVec &args) {
            UTIL_ASSERT(Util::Err::NotSupported, args.size() > 1,
                        ".args should have at least 2 items, report this");
            Op::FlatArgs a;
            a.reserve(args.size());
            for (const auto &i : args) {
                a.emplace_back(std::get<Expr::BasePtr>(i));
            }
            return Create::concat(std::move(a));
        }

        /** Abstraction function for Z3_OP_SIGN_EXT */
        static Expr::BasePtr sign_ext(const ArgsVec &args, const z3::func_decl &decl) {
            const auto &ctx { decl.ctx() };
            M_UINT_BINARY(Create::sign_ext);
        }

        /** Abstraction function for Z3_OP_ZERO_EXT */
        static Expr::BasePtr zero_ext(const ArgsVec &args, const z3::func_decl &decl) {
            const auto &ctx { decl.ctx() };
            M_UINT_BINARY(Create::zero_ext);
        }

        /** Abstraction function for Z3_OP_EXTRACT */
        static Expr::BasePtr extract(const ArgsVec &args, const z3::expr &e) {
            M_ASSERT_ARG_LEN(args, 1);
            return Create::extract(e.hi(), e.lo(), M_GET_EARG(0));
        }

        /**********************************************************/
        /*                     Floating Point                     */
        /**********************************************************/

        /** A struct meant for certain FP abstractions */
        struct FP final {
          private:
            /** std::copysign if Real is signed, else return x */
            template <Mode::Sign::Real Sign, typename T> static constexpr T copysign(const T x) {
                if constexpr (Sign != Mode::Sign::Real::None) {
                    return std::copysign(x, T { Util::to_underlying(Sign) });
                }
                return x;
            }

            /** A helper function to assist in creating FPA literals */
            template <Mode::Sign::Real Sign>
            static Expr::BasePtr fpa_literal(const z3::expr &b_obj, const double dbl,
                                             const float flt) {
                const auto sort { b_obj.get_sort() };
                const auto width { z3_sort_to_fp_width(sort) };
                if (LIKELY(width == Mode::FP::dbl)) {
                    return Create::literal(copysign<Sign>(dbl));
                }
                if (LIKELY(width == Mode::FP::flt)) {
                    return Create::literal(copysign<Sign>(flt));
                }
                UTIL_THROW(Error::Backend::Unsupported, M_REFUSE_FP_STANDARD "\nSort: ", sort);
            }

            /** A helper function to assist in creating FPA literals
             *  A specialization which use a Mode::Sign::FP
             */
            template <Mode::Sign::FP Sign, typename... Args>
            static auto fpa_literal(Args &&...args) {
                return fpa_literal<Mode::Sign::to_real(Sign)>(std::forward<Args>(args)...);
            }

            // Conversions
          public:
            /** Abstraction function for Z3_OP_FPA_TO_SBV */
            static Expr::BasePtr to_bv_signed(const ArgsVec &args, const z3::func_decl &decl) {
                M_ASSERT_ARG_LEN(args, 2);
                return Create::FP::to_bv_signed(
                    std::get<Mode::FP::Rounding>(args[0]), M_GET_EARG(1),
                    static_cast<U64>(Z3_get_decl_int_parameter(decl.ctx(), decl, 0)), {});
            }
            /** Abstraction function for Z3_OP_FPA_TO_UBV */
            static Expr::BasePtr to_bv_unsigned(const ArgsVec &args, const z3::func_decl &decl) {
                M_ASSERT_ARG_LEN(args, 2);
                return Create::FP::to_bv_unsigned(
                    std::get<Mode::FP::Rounding>(args[0]), M_GET_EARG(1),
                    static_cast<U64>(Z3_get_decl_int_parameter(decl.ctx(), decl, 0)), {});
            }

            /** Abstraction function for Z3_OP_FPA_IS_NAN */
            static Expr::BasePtr is_nan(const ArgsVec &args) { M_UNARY(Create::FP::is_nan); }

            /** Abstraction function for Z3_OP_FPA_TO_IEEE_BV */
            static Expr::BasePtr to_ieee_bv(const ArgsVec &args) {
                M_UNARY(Create::FP::to_ieee_bv);
            }

            /** Abstraction function for Z3_OP_FPA_TO_FP
             *  TODO
             */
            static Expr::BasePtr to_fp(const ArgsVec &args) {
                (void) args;
                throw Util::Err::NotSupported("This is not yet supported");
            }

            /** Abstraction function for Z3_OP_FPA_NUM to a primtive type
             *  Note: this function can only handle 32 bit and 64 bit floats
             */
            static std::variant<double, float> num_primitive(const z3::expr &b_obj) {
                const auto &ctx { b_obj.ctx() };

                // To extend this function to handle bigger floats, we need to use these functions:
                //   z3.Z3_fpa_get_numeral_significand_string (has the leading 1. or 0.)
                //   z3.Z3_fpa_get_numeral_exponent_string

                // Fp components (z3 needs unit64_t and int64_t)
                int sign;          // NOLINT
                uint64_t mantissa; // NOLINT
                int64_t exp;       // NOLINT

                // Extract fp components (success is false if the size is too large)
                bool success { Z3_fpa_get_numeral_sign(ctx, b_obj, &sign) };
                success &= Z3_fpa_get_numeral_significand_uint64(ctx, b_obj, &mantissa);
                success &= Z3_fpa_get_numeral_exponent_int64(ctx, b_obj, &exp, true);

                // Error check
                UTIL_ASSERT(
                    Util::Err::Unknown, success,
                    "something went wrong with fp component extraction.\nGiven fp: ", b_obj);

                const auto sort { b_obj.get_sort() };
                const auto width { z3_sort_to_fp_width(sort) };
                namespace FP = Mode::FP;
                if (LIKELY(width == FP::dbl)) {
                    const U64 to_val { (Util::widen<U64, true>(sign) << FP::dbl.no_sign_width()) |
                                       static_cast<U64>(mantissa) |
                                       (Util::unsign(static_cast<I64>(exp))
                                        << FP::dbl.mantissa_raw()) };
                    // If nothing went wrong, this reinterpret_cast should be safe
                    double ret; // NOLINT
                    UTIL_TYPE_PUN_ONTO(&ret, &to_val);
                    return ret;
                }
                if (LIKELY(width == FP::flt)) {
                    const uint32_t to_val { (Util::unsign(sign) << FP::flt.no_sign_width()) |
                                            Util::narrow<uint32_t>(mantissa) |
                                            (Util::narrow<uint32_t, true>(exp)
                                             << FP::flt.mantissa_raw()) };
                    // If nothing went wrong, this reinterpret_cast should be safe
                    float ret; // NOLINT
                    UTIL_TYPE_PUN_ONTO(&ret, &to_val);
                    return ret;
                }
                UTIL_THROW(
                    Util::Err::NotSupported,
                    "Cannot create a value for this unknown floating point standard.\nZ3_sort: ",
                    sort);
            }

            /** Abstraction function for Z3_OP_FPA_NUM */
            static Expr::BasePtr num(const z3::expr &b_obj) {
                const std::variant<double, float> x { num_primitive((b_obj)) };
                if (LIKELY(x.index() == 0)) {
                    return Create::literal(std::get<double>(x));
                }
                return Create::literal(std::get<float>(x));
            }

            /** Abstraction function for fpa zeros */
            template <Mode::Sign::FP Sign> static Expr::BasePtr zero(const z3::expr &b_obj) {
                return fpa_literal<Sign>(b_obj, 0., 0.F);
            }

            /** Abstraction function for fpa inf */
            template <Mode::Sign::FP Sign> static Expr::BasePtr inf(const z3::expr &b_obj) {
                static_assert(std::numeric_limits<double>::is_iec559, "IEE 754 required for -inf");
                static_assert(std::numeric_limits<float>::is_iec559, "IEE 754 required for -inf");
                static const constexpr float inf_f { std::numeric_limits<float>::infinity() };
                static const constexpr double inf_d { std::numeric_limits<double>::infinity() };
                return fpa_literal<Sign>(b_obj, inf_d, inf_f);
            }

            /** Abstraction function for Z3_OP_FPA_NAN
             *  Note: SMT theory of floating point numbers only has one NaN, it does not
             *  distinguish between quiet and signalling NaNs.
             *  We choose quiet as the type of nan we return
             */
            static Expr::BasePtr nan(const z3::expr &b_obj) {
                namespace Z = ::Backend::Z3;
                return fpa_literal<Mode::Sign::Real::None>(b_obj, Z::nan<double>, Z::nan<float>);
            }

            // Arithmetic

            /** Abstraction function for Z3_OP_FPA_ADD */
            static Expr::BasePtr add(const ArgsVec &args) { M_MODEBINARY(Create::FP::add); }

            /** Abstraction function for Z3_OP_FPA_SUB */
            static Expr::BasePtr sub(const ArgsVec &args) { M_MODEBINARY(Create::FP::sub); }

            /** Abstraction function for Z3_OP_FPA_MUL */
            static Expr::BasePtr mul(const ArgsVec &args) { M_MODEBINARY(Create::FP::mul); }

            /** Abstraction function for Z3_OP_FPA_DIV */
            static Expr::BasePtr div(const ArgsVec &args) { M_MODEBINARY(Create::FP::div); }
        };

#undef M_REFUSE_FP_STANDARD
#undef M_ASSERT_ARG_LEN
#undef M_GET_EARG

#undef M_FLAT_BINARY
#undef M_MODEBINARY
#undef M_UINT_BINARY
#undef M_BINARY
#undef M_UNARY
    };

} // namespace Backend::Z3

#endif
