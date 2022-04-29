/**
 * @file
 * @brief This file defines how the Z3 backend converts Claricpp Exprs into Z3 ASTs
 */
#ifndef R_SRC_BACKEND_Z3_CONVERT_HPP_
#define R_SRC_BACKEND_Z3_CONVERT_HPP_

#include "constants.hpp"
#include "width_translation.hpp"

#include "../../op.hpp"


/********************************************************************/
/*                    Claricpp -> Z3 Conversion                     */
/********************************************************************/


namespace Backend::Z3 {

    /** Used to convert Claricpp exprs into Z3 ASTs */
    template <typename Z3> struct Convert final {
        static_assert(typename Z3::IsZ3Bk(), "Z3 should be the Z3 backend");

      private:
        /** The size of a float */
        static constexpr inline const auto flt_size { 4_ui * BitLength::char_bit };

        /** A function that narrows a U64 to Z3's unsigned type */
        static constexpr auto to_z3u(const U64 x) { return Util::narrow<unsigned>(x); }

      public:
        // Unary

        /** Negation converter */
        static z3::expr neg(const z3::expr &e) { return -e; }

        /** Abs converter */
        static z3::expr abs(const z3::expr &e) { return z3::abs(e); }

        /** Not converter */
        static z3::expr not_(const z3::expr &e) { return not e; }

        /** Invert converter */
        static z3::expr invert(const z3::expr &e) { return ~e; }

        /** Reverse converter */
        static z3::expr reverse(const z3::expr &e) {
            const auto size { e.get_sort().bv_size() };

            // Trivial case
            if (size == CHAR_BIT) {
                return e;
            }

            // Error checking
            using E = Error::Expr::Operation;
            UTIL_ASSERT(E, size % CHAR_BIT == 0, "Can't reverse non-byte sized bitvectors");

            // Reverse byte by byte
            auto ret { extract(CHAR_BIT - 1u, 0u, e) };
            for (U64 i = CHAR_BIT; i < size; i += CHAR_BIT) {
                const auto tmp { extract(to_z3u(i + CHAR_BIT - 1), to_z3u(i), e) };
                ret = concat(ret, tmp);
            }
            return ret;
        }

        // UIntBinary

        /** Sign Extension converter */
        static z3::expr signext(const z3::expr &e, const U64 i) { return z3::sext(e, to_z3u(i)); }

        /** Zero Extension converter */
        static z3::expr zeroext(const z3::expr &e, const U64 i) { return z3::zext(e, to_z3u(i)); }

        // Binary

        /** Equality comparison converter */
        static z3::expr eq(const z3::expr &l, const z3::expr &r) {
            if (l.is_fpa()) {
                return z3::fp_eq(l, r);
            }
            return l == r;
        }

        /** Not-equals comparison converter */
        static z3::expr neq(const z3::expr &l, const z3::expr &r) { return l != r; }

        /** Compare converter */
        template <Mode::Compare M> static z3::expr compare(const z3::expr &l, const z3::expr &r) {
            using C = Mode::Compare;
            if constexpr (M == C::SLE) {
                if (l.is_fpa()) {
                    return l <= r;
                }
                else {
                    return z3::sle(l, r);
                }
            }
            else if constexpr (M == C::SLT) {
                if (l.is_fpa()) {
                    return l < r;
                }
                else {
                    return z3::slt(l, r);
                }
            }
            else if constexpr (M == C::SGE) {
                if (l.is_fpa()) {
                    return l >= r;
                }
                else {
                    return z3::sge(l, r);
                }
            }
            else if constexpr (M == C::SGT) {
                if (l.is_fpa()) {
                    return l > r;
                }
                else {
                    return z3::sgt(l, r);
                }
            }
            else if constexpr (M == C::ULE) {
                return z3::ule(l, r);
            }
            else if constexpr (M == C::ULT) {
                return z3::ult(l, r);
            }
            else if constexpr (M == C::UGE) {
                return z3::uge(l, r);
            }
            else if constexpr (M == C::UGT) {
                return z3::ugt(l, r);
            }
            else {
                static_assert(Util::CD::false_<M>, "Invalid mode");
            }
        }

        /** Subtraction converter */
        static z3::expr sub(const z3::expr &l, const z3::expr &r) { return l - r; }

        /** Division converter */
        template <Mode::Signed Sgn> static z3::expr div(const z3::expr &l, const z3::expr &r) {
            if constexpr (Sgn == Mode::Signed::Signed) {
                return l / r;
            }
            else {
                return z3::udiv(l, r);
            }
        }

        /** Mod converter
         *  Note we use rem (because of the difference between C and Python % operators)
         */
        template <Mode::Signed Sgn> static z3::expr mod(const z3::expr &l, const z3::expr &r) {
            if constexpr (Sgn == Mode::Signed::Signed) {
                return z3::srem(l, r);
            }
            else {
                return z3::urem(l, r);
            }
        }

        /** Shift converter */
        template <Mode::Shift Mask> static z3::expr shift(const z3::expr &l, const z3::expr &r) {
            using S = Mode::Shift;
            if constexpr (Mask == S::Left) {
                return z3::shl(l, r);
            }
            else if constexpr (Mask == S::ArithmeticRight) {
                return z3::ashr(l, r);
            }
            else if constexpr (Mask == S::LogicalRight) {
                return z3::lshr(l, r);
            }
            else {
                static_assert(Util::CD::false_<Mask>, "Unsupported mask mode");
            }
        }

        /** Rotate converter */
        template <Mode::LR LR> static z3::expr rotate(const z3::expr &l, const z3::expr &r) {
            // z3's C++ API's rotate functions are different (note the "ext" below)
            using namespace Z3;
            z3::expr ret { l.ctx(),
                           (LR == Mode::LR::Left ? Z3_mk_ext_rotate_left(l.ctx(), l, r)
                                                 : Z3_mk_ext_rotate_right(l.ctx(), l, r)) };
            l.ctx().check_error();
            return ret;
        }

        /** Concat converter */
        static z3::expr concat(const z3::expr &l, const z3::expr &r) { return z3::concat(l, r); }

        // Flat

        /** The type of argument a flat function takes in */
        using FlatArr = CTSC<z3::expr> *const;

      private:
        /** Like C++20's version of std::accumulate, except it works with pointers */
        template <typename FunctorType>
        static z3::expr ptr_accumulate(FlatArr arr, const U64 size) {
#ifdef DEBUG
            UTIL_ASSERT(Util::Err::Size, size >= 2,
                        "size < 2; this probably resulted from an invalid claricpp expr.");
            UTIL_ASSERT_NOT_NULL_DEBUG(arr[0]);
            UTIL_ASSERT_NOT_NULL_DEBUG(arr[1]);
#endif
            const FunctorType fn {};
            z3::expr ret { fn(*arr[0], *arr[1]) };
            for (U64 i { 2 }; i < size; ++i) {
                UTIL_ASSERT_NOT_NULL_DEBUG(arr[i]);
                ret = std::move(fn(std::move(ret), *arr[i]));
            }
            return ret;
        }

      public:
        /** Add converter */
        static z3::expr add(FlatArr arr, const U64 size) {
            return ptr_accumulate<std::plus<z3::expr>>(arr, size);
        }

        /** Mul converter */
        static z3::expr mul(FlatArr arr, const U64 size) {
            return ptr_accumulate<std::multiplies<z3::expr>>(arr, size);
        }

        /** Or converter */
        static z3::expr or_(FlatArr arr, const U64 size) {
            // Note that Z3's bit or auto switched to logical or for booleans
            return ptr_accumulate<std::bit_or<z3::expr>>(arr, size);
        }

        /** And converter */
        static z3::expr and_(FlatArr arr, const U64 size) {
            // Note that Z3's bit and auto switched to logical and for booleans
            return ptr_accumulate<std::bit_and<z3::expr>>(arr, size);
        }

        /** Xor converter */
        static z3::expr xor_(FlatArr arr, const U64 size) {
            return ptr_accumulate<std::bit_xor<z3::expr>>(arr, size);
        }

        // Other

        /** Extract converter */
        static z3::expr extract(const U64 high, const U64 low, const z3::expr &e) {
            return e.extract(to_z3u(high), to_z3u(low));
        }

        /** If converter */
        static z3::expr if_(const z3::expr &cond, const z3::expr &if_true,
                            const z3::expr &if_false) {
            return z3::ite(cond, if_true, if_false);
        }

        /** Literal converter
         *  expr may not be nullptr
         */
        static z3::expr literal(const Expr::RawPtr expr, z3::context &ctx) {
            UTIL_ASSERT_NOT_NULL_DEBUG(expr);
            UTIL_ASSERT_NOT_NULL_DEBUG(expr->op); // Sanity check
            using To = CTSC<Op::Literal>;
            const auto &data { Util::checked_static_cast<To>(expr->op.get())->value };
            try {
                switch (data.index()) {
#define M_CASE(TYPE, EXPR)                                                                         \
    case Util::Type::index<decltype(data), TYPE>: {                                                \
        const auto &got { std::get<TYPE>(data) };                                                  \
        return (EXPR);                                                                             \
    }
                    M_CASE(bool, ctx.bool_val(got));
                    M_CASE(std::string, ctx.string_val(got));
                    M_CASE(float, ctx.fpa_val(got));
                    M_CASE(double, ctx.fpa_val(got));
                    case Util::Type::index<decltype(data), PyObj::VSPtr>: {
                        UTIL_THROW(Error::Backend::Unsupported,
                                   "VSA is not supported by the Z3 backend");
                    }
                        M_CASE(uint8_t, ctx.bv_val(got, 8));
                        M_CASE(uint16_t, ctx.bv_val(got, 16));
                        M_CASE(uint32_t, ctx.bv_val(got, 32));
                        M_CASE(uint64_t, ctx.bv_val(static_cast<uint64_t>(got), 64));
#undef M_CASE
                    case Util::Type::index<decltype(data), BigInt>: {
                        const auto &big { std::get<BigInt>(data) };
                        if (std::holds_alternative<BigInt::Str>(big.value)) {
                            return ctx.bv_val(std::get<BigInt::Str>(big.value).c_str(),
                                              to_z3u(big.bit_length));
                        }
                        else {
                            std::ostringstream s;
                            s << big.value; // z3 needs this as a str :/
                            return ctx.bv_val(s.str().c_str(), to_z3u(big.bit_length));
                        }
                    }
                        // Error handling
                    default:
                        UTIL_THROW(Util::Err::NotSupported,
                                   "Unknown variant type in literal op given to z3 backend");
                }
            }
            // Re-emit these exceptions with additional info and wrapped as a Claricpp exception
            catch (const std::bad_variant_access &ex) {
                UTIL_THROW(Util::Err::BadVariantAccess, ex.what());
            }
        }

        /** Symbol converter
         *  This saves symbol annotation for later translocation
         *  expr may not be nullptr
         */
        static z3::expr symbol(const Expr::RawPtr expr, SymAnTransData &satd, z3::context &ctx) {
            UTIL_ASSERT_NOT_NULL_DEBUG(expr);
            UTIL_ASSERT_NOT_NULL_DEBUG(expr->op); // Sanity check
            using To = CTSC<Op::Symbol>;
            const std::string &name { Util::checked_static_cast<To>(expr->op.get())->name };
            switch (expr->cuid) {
                case Expr::Bool::static_cuid:
                    return ctx.bool_const(name.c_str());
                case Expr::String::static_cuid:
                    return ctx.string_const(name.c_str());
                case Expr::FP::static_cuid: {
                    using FPP = CTSC<Expr::FP>;
                    const auto fpw { (Util::checked_static_cast<FPP>(expr)->bit_length == flt_size)
                                         ? Mode::FP::flt
                                         : Mode::FP::dbl };
                    return ctx.fpa_const(name.c_str(), fpw.exp, fpw.mantissa);
                }
                case Expr::BV::static_cuid: {
                    using BVP = CTSC<Expr::BV>;
#ifdef DEBUG // @todo Double check if I am strill right
                    UTIL_ASSERT(Util::Err::Unknown,
                                Factory::Private::gcache<Expr::Base>().find(expr->hash),
                                "cache lookup failed for existing object");
#endif
                    // Update annotations for translocation
                    const U64 name_hash { Util::FNV1a<char>::hash(name.c_str(), name.size()) };
                    if (expr->annotations) {
                        Util::map_emplace(satd, name_hash, expr->annotations);
                    }
                    else {
                        satd.erase(name_hash);
                    }
                    // Return the converted constant
                    const U64 bit_length { Util::checked_static_cast<BVP>(expr)->bit_length };
                    return ctx.bv_const(name.c_str(), to_z3u(bit_length));
                }
                // Error handling
                case Expr::VS::static_cuid:
                    UTIL_THROW(Error::Backend::Unsupported,
                               "VSA is not supported by the Z3 backend");
                default:
                    UTIL_THROW(Util::Err::NotSupported, "Unknown expr CUID given to z3 backend");
            }
        }

        /** A struct meant for certain FP conversions */
        struct FP final {
          private:
            /** Verifies 2 exprs are FPs with the same context */
            static void assert_are_compatible(const z3::expr &a, const z3::expr &b) {
#ifdef DEBUG
                z3::check_context(a, b);
                UTIL_ASSERT(Util::Err::Type, a.is_fpa() && b.is_fpa(), " called non-FP ops");
#else
                Util::sink(a, b);
#endif
            }

            /** Converts a claricpp rounding mode to a z3 rounding mode */
            static constexpr z3::rounding_mode to_z3_rm(const Mode::FP::Rounding mode) {
                switch (mode) {
                    case Mode::FP::Rounding::NearestTiesAwayFromZero:
                        return z3::RNA;
                    case Mode::FP::Rounding::NearestTiesEven:
                        return z3::RNE;
                    case Mode::FP::Rounding::TowardsNegativeInf:
                        return z3::RTN;
                    case Mode::FP::Rounding::TowardsPositiveInf:
                        return z3::RTP;
                    case Mode::FP::Rounding::TowardsZero:
                        return z3::RTZ;
                    default:
                        UTIL_THROW(Util::Err::NotSupported, "Unable to map Mode::FP::Rounding ",
                                   mode, " to z3::rounding_mode");
                };
            }

          public:
            /** ToIEEEBV converter */
            static z3::expr to_ieee_bv(const z3::expr &e) {
                return e.mk_to_ieee_bv();
            }

            /** FP::Add converter */
            static z3::expr add(const Mode::FP::Rounding mode, const z3::expr &l,
                                const z3::expr &r) {
                l.ctx().set_rounding_mode(to_z3_rm(mode));
                return l + r;
            }

            /** FP::Sub converter */
            static z3::expr sub(const Mode::FP::Rounding mode, const z3::expr &l,
                                const z3::expr &r) {
                l.ctx().set_rounding_mode(to_z3_rm(mode));
                return l - r;
            }

            /** FP::Mul converter */
            static z3::expr mul(const Mode::FP::Rounding mode, const z3::expr &l,
                                const z3::expr &r) {
                l.ctx().set_rounding_mode(to_z3_rm(mode));
                return l * r;
            }

            /** FP::Div converter */
            static z3::expr div(const Mode::FP::Rounding mode, const z3::expr &l,
                                const z3::expr &r) {
                l.ctx().set_rounding_mode(to_z3_rm(mode));
                return l / r;
            }

            // Other

            /** FP::ToBV converter */
            template <Mode::Signed Sgn>
            static z3::expr to_bv(const Mode::FP::Rounding mode, const z3::expr &e,
                                  const U64 bit_length) {
                e.ctx().set_rounding_mode(to_z3_rm(mode));
                if constexpr (Sgn == Mode::Signed::Signed) {
                    return z3::fpa_to_sbv(e, to_z3u(bit_length));
                }
                else {
                    return z3::fpa_to_ubv(e, to_z3u(bit_length));
                }
            }

            /** FP::FromFP converter */
            static z3::expr from_fp(const Mode::FP::Rounding mode, const z3::expr &e,
                                    const Mode::FP::Width &width) {
                auto &ctx { e.ctx() };
                ctx.set_rounding_mode(to_z3_rm(mode));
                return z3::fpa_to_fpa(e, fp_width_to_z3_sort(ctx, width));
            }

            /** FP::From2sComplementBV converter */
            template <Mode::Signed Sgn>
            static z3::expr from_2s_complement_bv(const Mode::FP::Rounding mode, const z3::expr &e,
                                                  const Mode::FP::Width &width) {
                auto &ctx { e.ctx() };
                ctx.set_rounding_mode(to_z3_rm(mode));
                if constexpr (Sgn == Mode::Signed::Signed) {
                    return z3::sbv_to_fpa(e, fp_width_to_z3_sort(ctx, width));
                }
                else {
                    return z3::ubv_to_fpa(e, fp_width_to_z3_sort(ctx, width));
                }
            }

            /** FP::FromNot2sComplementBV converter */
            static z3::expr from_not_2s_complement_bv(const z3::expr &e,
                                                      const Mode::FP::Width &width) {
                return e.mk_from_ieee_bv(fp_width_to_z3_sort(e.ctx(), width));
            }
        };

        /** A struct meant for certain String conversions */
        struct String final {

            /** FromInt converter
             *  \todo double check
             */
            static z3::expr from_int(const z3::expr &e) { return z3::bv2int(e, false).itos(); }

            // Int Binary

            /** ToInt converter */
            static z3::expr to_int(const z3::expr &e, const U64 len) {
                const auto a { e.stoi() };
                return z3::int2bv(to_z3u(len), a);
            }

            /** Len converter */
            static z3::expr len(const z3::expr &e, const U64 len) {
                const auto a { e.length() };
                return z3::int2bv(to_z3u(len), a);
            }

            // Binary

            /** Contains converter */
            static z3::expr contains(const z3::expr &full, const z3::expr &sub) {
                return full.contains(sub);
            }

            /** PrefixOf converter */
            static z3::expr prefix_of(const z3::expr &full, const z3::expr &prefix) {
                return z3::prefixof(full, prefix);
            }

            /** SuffixOf converter */
            static z3::expr suffix_of(const z3::expr &full, const z3::expr &suffix) {
                return z3::suffixof(full, suffix);
            }

            // Ternary

            /** Replace converter */
            static z3::expr replace(const z3::expr &full, const z3::expr &search,
                                    const z3::expr &replacement) {
                return full.replace(search, replacement);
            }

            /** SubString converter */
            static z3::expr substring(const z3::expr &full, const z3::expr &offset,
                                      const z3::expr &len) {
                const auto a { z3::bv2int(offset, false) };
                const auto b { z3::bv2int(len, false) };
                return full.extract(a, b);
            }

            // Other

            /** IndexOf converter */
            static z3::expr index_of(const z3::expr &str, const z3::expr &pattern,
                                     const z3::expr &start_index, const U64 bit_length) {
                const auto a { z3::indexof(str, pattern, start_index) };
                return z3::int2bv(to_z3u(bit_length), a);
            }
        };
    };

} // namespace Backend::Z3

#endif
