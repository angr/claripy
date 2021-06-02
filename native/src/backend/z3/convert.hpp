/**
 * @file
 * @brief This file defines how the Z3 backend converts Claricpp Expressions into Z3 ASTs
 */
#ifndef R_BACKEND_Z3_CONVERT_HPP_
#define R_BACKEND_Z3_CONVERT_HPP_

#include "constants.hpp"
#include "fp_width.hpp"
#include "tl_ctx.hpp"

#include "../../op.hpp"


/********************************************************************/
/*                    Claricpp -> Z3 Conversion                     */
/********************************************************************/


namespace Backend::Z3::Convert {

    // Forward declarations
    z3::expr concat(const z3::expr &l, const z3::expr &r);
    z3::expr extract(const Constants::UInt high, const Constants::UInt low, const z3::expr &e);

    namespace Private {

        /** A hack copied from python that *should* be removed ASAP
         *  @todo Remove the need for this
         *  Python comment: XXX this is a HUGE HACK that should be removed whenever uninitialized
         *  gets moved to the "proposed annotation backend" or wherever will prevent it from being
         *  part of the object identity. also whenever the VSA attributes get the fuck out of BVS
         * as well
         */
        inline thread_local std::map<std::string, const Expression::BasePtr> extra_bvs_data;

        /** The size of a float
         *  Note that constexpr may not imply inline here so we are explicit
         */
        static inline constexpr const auto flt_size { 4_ui * BitLength::char_bit };

    } // namespace Private

    // Unary

    /** Negation converter */
    inline z3::expr neg(const z3::expr &e) { return -e; }

    /** Abs converter */
    inline z3::expr abs(const z3::expr &e) { return z3::abs(e); }

    /** Invert converter */
    inline z3::expr invert(const z3::expr &e) { return ~e; }

    /** Reverse converter */
    inline z3::expr reverse(const z3::expr &e) {
        const auto size { e.length().get_numeral_uint64() };

        // Trivial case
        if (size == C_CHAR_BIT) {
            return e;
        }

        // Error checking
        using Err = Error::Expression::Operation;
        Utils::affirm<Err>(size % C_CHAR_BIT == 0, "Can't reverse non-byte sized bitvectors");

        // Reverse byte by byte
        auto ret { extract(Utils::narrow<z3u>(C_CHAR_BIT - 1), Utils::narrow<z3u>(0), e) };
        for (Constants::UInt i = C_CHAR_BIT; i < size; i += C_CHAR_BIT) {
            ret = ::Backend::Z3::Convert::concat(
                ret, // Move?
                extract(Utils::narrow<z3u>(i + C_CHAR_BIT - 1), Utils::narrow<z3u>(i), e));
        }
        return ret;
    }

    // UIntBinary

    /** Sign Extension converter */
    inline z3::expr signext(const z3::expr &e, const Constants::UInt i) {
        return z3::sext(e, Utils::narrow<z3u>(i));
    }

    /** Zero Extension converter */
    inline z3::expr zeroext(const z3::expr &e, const Constants::UInt i) {
        return z3::zext(e, Utils::narrow<z3u>(i));
    }

    // Binary

    /** Equality comparisson converter */
    inline z3::expr eq(const z3::expr &l, const z3::expr &r) { return l == r; }

    /** Not-equals comparisson converter */
    inline z3::expr neq(const z3::expr &l, const z3::expr &r) { return l != r; }

    /** Compare converter */
    template <Mode::Compare Mask> inline z3::expr compare(const z3::expr &l, const z3::expr &r) {
        using C = Mode::Compare;
        static_assert(Mode::compare_is_valid(Mask), "Invalid mask mode");
        if constexpr (Utils::BitMask::has(Mask, C::Signed | C::Less | C::Eq)) {
            return z3::sle(l, r);
        }
        else if constexpr (Utils::BitMask::has(Mask, C::Signed | C::Less | C::Neq)) {
            return z3::slt(l, r);
        }
        else if constexpr (Utils::BitMask::has(Mask, C::Signed | C::Greater | C::Eq)) {
            return z3::sge(l, r);
        }
        else if constexpr (Utils::BitMask::has(Mask, C::Signed | C::Greater | C::Neq)) {
            return z3::sgt(l, r);
        }
        else if constexpr (Utils::BitMask::has(Mask, C::Unsigned | C::Less | C::Eq)) {
            return z3::ult(l, r);
        }
        else if constexpr (Utils::BitMask::has(Mask, C::Unsigned | C::Less | C::Neq)) {
            return z3::ult(l, r);
        }
        else if constexpr (Utils::BitMask::has(Mask, C::Unsigned | C::Greater | C::Eq)) {
            return z3::uge(l, r);
        }
        else if constexpr (Utils::BitMask::has(Mask, C::Unsigned | C::Greater | C::Neq)) {
            return z3::ugt(l, r);
        }
        else {
            static_assert(Utils::CD::false_<Mask>, "Unsupported mask mode");
        }
    }

    /** Subtraction converter */
    inline z3::expr sub(const z3::expr &l, const z3::expr &r) { return l - r; }

    /** Division converter */
    template <bool Signed> z3::expr div(const z3::expr &l, const z3::expr &r) {
        if constexpr (Signed) {
            return l / r;
        }
        else {
            return z3::udiv(l, r);
        }
    }

    /** Pow converter */
    inline z3::expr pow(const z3::expr &l, const z3::expr &r) { return z3::pw(l, r); }

    /** Mod converter */
    template <bool Signed> z3::expr mod(const z3::expr &l, const z3::expr &r) {
        if constexpr (Signed) {
            return z3::smod(l, r);
        }
        else {
            return z3::mod(l, r);
        }
    }

    /** Shift converter */
    template <Mode::Shift Mask> z3::expr shift(const z3::expr &l, const z3::expr &r) {
        using S = Mode::Shift;
        static_assert(Mode::shift_is_valid(Mask), "Invalid mask mode");
        if constexpr (Utils::BitMask::has(Mask, S::Arithmetic | S::Left)) {
            return z3::shl(l, r);
        }
        else if constexpr (Utils::BitMask::has(Mask, S::Arithmetic | S::Right)) {
            return z3::ashr(l, r);
        }
        else if constexpr (Utils::BitMask::has(Mask, S::Logical | S::Right)) {
            return z3::lshr(l, r);
        }
        else {
            static_assert(Utils::CD::false_<Mask>, "Unsupported mask mode");
        }
    }

    /** Rotate converter */
    template <bool Left> z3::expr rotate(const z3::expr &l, const z3::expr &r) {
        // z3's C++ API's rotate functions are different (note the "ext" below)
        using namespace Z3;
        auto &ctx { ::Backend::Z3::Private::tl_ctx };
        z3::expr ret { ctx, (Left ? Z3_mk_ext_rotate_left(ctx, l, r)
                                  : Z3_mk_ext_rotate_right(ctx, l, r)) };
        ctx.check_error();
        return ret;
    }

    /** Concat converter */
    z3::expr concat(const z3::expr &l, const z3::expr &r) { return z3::concat(l, r); }

    // Flat

    /** The type of argument a flat function takes in */
    using FlatArr = Constants::CTSC<z3::expr> *const;

    namespace Private {

        /** Like C++20's version of std::accumulate, except it works with pointers */
        template <typename FunctorType>
        inline z3::expr ptr_accumulate(FlatArr arr, const Constants::UInt size) {
#ifdef DEBUG
            Utils::affirm<Utils::Error::Unexpected::Size>(
                size >= 2,
                "size < 2; this probably resulted from an invalid claricpp expression.");
#endif
            const FunctorType fn {};
            z3::expr ret { fn(*arr[0], *arr[1]) };
            for (Constants::UInt i { 2 }; i < size; ++i) {
                ret = std::move(fn(std::move(ret), *arr[i]));
            }
            return ret;
        }
    } // namespace Private

    /** Add converter */
    inline z3::expr add(FlatArr arr, const Constants::UInt size) {
        return Private::ptr_accumulate<std::plus<z3::expr>>(arr, size);
    }

    /** Mul converter */
    inline z3::expr mul(FlatArr arr, const Constants::UInt size) {
        return Private::ptr_accumulate<std::multiplies<z3::expr>>(arr, size);
    }

    /** Or converter */
    inline z3::expr or_(FlatArr arr, const Constants::UInt size) {
        // Note that Z3's bit or auto switched to logical or for booleans
        return Private::ptr_accumulate<std::bit_or<z3::expr>>(arr, size);
    }

    /** And converter */
    inline z3::expr and_(FlatArr arr, const Constants::UInt size) {
        // Note that Z3's bit and auto switched to logical and for booleans
        return Private::ptr_accumulate<std::bit_and<z3::expr>>(arr, size);
    }

    /** Xor converter */
    inline z3::expr xor_(FlatArr arr, const Constants::UInt size) {
        return Private::ptr_accumulate<std::bit_xor<z3::expr>>(arr, size);
    }

    // Other

    /** Extract converter */
    inline z3::expr extract(const Constants::UInt high, const Constants::UInt low,
                            const z3::expr &e) {
        return e.extract(Utils::narrow<z3u>(high), Utils::narrow<z3u>(low));
    }

    /** If converter */
    inline z3::expr if_(const z3::expr &cond, const z3::expr &if_true, const z3::expr &if_false) {
        return z3::ite(cond, if_true, if_false);
    }

    /** Literal converter */
    inline z3::expr literal(const Expression::RawPtr expr) {
        using To = Constants::CTSC<Op::Literal>;
        const auto &data { Utils::checked_static_cast<To>(expr->op.get())->value };
        auto &ctx { ::Backend::Z3::Private::tl_ctx };
        try {
            switch (expr->cuid) {
                case Expression::Bool::static_cuid:
                    return ctx.bool_val(std::get<bool>(data));
                case Expression::String::static_cuid:
                    return ctx.string_val(std::get<std::string>(data));
                case Expression::FP::static_cuid: {
                    return (Expression::get_bit_length(expr) == Private::flt_size)
                             ? ctx.fpa_val(std::get<float>(data))
                             : ctx.fpa_val(std::get<double>(data));
                }
                case Expression::BV::static_cuid: {
                    const auto &vec { std::get<std::vector<char>>(data) };
                    return ctx.bv_val(vec.data(), Utils::narrow<z3u>(vec.size()));
                }
                    // Error handling
                case Expression::VS::static_cuid:
                    throw Error::Backend::Unsupported(WHOAMI_WITH_SOURCE
                                                      "VSA is not supported by the Z3 backend");
                default:
                    throw Utils::Error::Unexpected::NotSupported(
                        WHOAMI_WITH_SOURCE "Unknown expression CUID given to z3 backend");
            }
        }
        // Re-emit these exceptions with additional info and wrapped as a Claricpp exception
        catch (const std::bad_variant_access &ex) {
            throw Utils::Error::Unexpected::BadVariantAccess(WHOAMI_WITH_SOURCE, ex.what());
        }
    }

    /** Symbol converter
     *  to handle the extra_bvs_data hack, this uses a hack of viewing the private data of factory
     *  @todo remove the hack
     */
    inline z3::expr symbol(const Expression::RawPtr expr) {
        using To = Constants::CTSC<Op::Symbol>;
        const std::string &name { Utils::checked_static_cast<To>(expr->op.get())->name };
        auto &ctx { ::Backend::Z3::Private::tl_ctx };
        switch (expr->cuid) {
            case Expression::Bool::static_cuid:
                return ctx.bool_const(name.c_str());
            case Expression::String::static_cuid:
                return ctx.string_const(name.c_str());
            case Expression::FP::static_cuid: {
                using FPP = Constants::CTSC<Expression::FP>;
                const auto fpw { (Utils::checked_static_cast<FPP>(expr)->bit_length ==
                                  Private::flt_size)
                                     ? FP::flt
                                     : FP::dbl };
                return ctx.fpa_const(name.c_str(), Utils::narrow<z3u>(fpw.exp),
                                     Utils::narrow<z3u>(fpw.mantissa));
            }
            case Expression::BV::static_cuid: {
                using BVP = Constants::CTSC<Expression::FP>;
#ifdef DEBUG
                Utils::affirm<Utils::Error::Unexpected::Unknown>(
                    Factory::Private::cache<Expression::Base>.find(expr->hash) != nullptr,
                    WHOAMI_WITH_SOURCE "cache lookup failed for existing object");
#endif
                // This is a hack take from python
                Private::extra_bvs_data.emplace(
                    name, Factory::Private::cache<Expression::Base>.find(expr->hash));
                // Return the converted constant
                const Constants::UInt bit_length {
                    Utils::checked_static_cast<BVP>(expr)->bit_length
                };
                return ctx.bv_const(name.c_str(), Utils::narrow<z3u>(bit_length));
            }
                // Error handling
            case Expression::VS::static_cuid:
                throw Error::Backend::Unsupported(WHOAMI_WITH_SOURCE
                                                  "VSA is not supported by the Z3 backend");
            default:
                throw Utils::Error::Unexpected::NotSupported(
                    WHOAMI_WITH_SOURCE "Unknown expression CUID given to z3 backend");
        }
    }

    namespace FP {

        /** IsInf converter */
        inline z3::expr is_inf(const z3::expr &e) { return e.mk_is_inf(); }

        /** IsNan converter */
        inline z3::expr is_nan(const z3::expr &e) { return e.mk_is_nan(); }

        /** ToIEEEBV converter */
        inline z3::expr to_ieee_bv(const z3::expr &e) { return e.mk_to_ieee_bv(); }

        // Mode Binary

        namespace Private {

            /** Verifes 2 expressions are FPs with the same context */
            inline void assert_are_compatible(const z3::expr &a, const z3::expr &b) {
#ifdef DEBUG
                z3::check_context(a, b);
                Utils::affirm<Utils::Error::Unexpected::Type>(
                    a.is_fpa() && b.is_fpa(), WHOAMI_WITH_SOURCE " called non-FP ops");
#else
                Utils::sink(a, b);
#endif
            }

            /** Converts a claricpp rounding mode to a z3 rounding mode */
            constexpr z3::rounding_mode to_z3_rm(const Mode::FP mode) {
                switch (mode) {
                    case Mode::FP::NearestTiesAwayFromZero:
                        return z3::RNA;
                    case Mode::FP::NearestTiesEven:
                        return z3::RNE;
                    case Mode::FP::TowardsNegativeInf:
                        return z3::RTN;
                    case Mode::FP::TowardsPositiveInf:
                        return z3::RTP;
                    case Mode::FP::TowardsZero:
                        return z3::RTZ;
                    default:
                        throw Utils::Error::Unexpected::NotSupported(
                            WHOAMI_WITH_SOURCE "Unable to map Mode::FP ", mode,
                            " to z3::rounding_mode");
                };
            }

        }; // namespace Private

        /** FP::Add converter */
        inline z3::expr add(const Mode::FP mode, const z3::expr &l, const z3::expr &r) {
            auto &ctx { ::Backend::Z3::Private::tl_ctx };
            ctx.set_rounding_mode(Private::to_z3_rm(mode));
            return l + r;
        }

        /** FP::Sub converter */
        inline z3::expr sub(const Mode::FP mode, const z3::expr &l, const z3::expr &r) {
            auto &ctx { ::Backend::Z3::Private::tl_ctx };
            ctx.set_rounding_mode(Private::to_z3_rm(mode));
            return l - r;
        }

        /** FP::Mul converter */
        inline z3::expr mul(const Mode::FP mode, const z3::expr &l, const z3::expr &r) {
            auto &ctx { ::Backend::Z3::Private::tl_ctx };
            ctx.set_rounding_mode(Private::to_z3_rm(mode));
            return l * r;
        }

        /** FP::Div converter */
        inline z3::expr div(const Mode::FP mode, const z3::expr &l, const z3::expr &r) {
            auto &ctx { ::Backend::Z3::Private::tl_ctx };
            ctx.set_rounding_mode(Private::to_z3_rm(mode));
            return l / r;
        }

        // Ternary

        /** FP::fp converter */
        inline z3::expr fp(const z3::expr &sgn, const z3::expr &exp, const z3::expr &sig) {
            return z3::fpa_fp(sgn, exp, sig);
        }

        // Other

        /** FP::ToBV converter */
        template <bool Signed>
        inline z3::expr to_bv(const Mode::FP mode, const z3::expr &e,
                              const Constants::UInt bit_length) {
            e.ctx().set_rounding_mode(Private::to_z3_rm(mode));
            if constexpr (Signed) {
                return z3::fpa_to_sbv(e, Utils::narrow<z3u>(bit_length));
            }
            else {
                return z3::fpa_to_ubv(e, Utils::narrow<z3u>(bit_length));
            }
        }


    } // namespace FP

    namespace String {

        /** FromInt converter */
        inline z3::expr from_int(const z3::expr &e) {
            return z3::bv2int(e, false).itos();
        } // todo?

        /** Unit converter */
        inline z3::expr unit(const z3::expr &e) { return e.unit(); }

        // Int Binary

        /** ToInt converter */
        inline z3::expr to_int(const z3::expr &e, const Constants::UInt len) {
            const auto a { e.stoi() };
            return z3::int2bv(Utils::narrow<z3u>(len), a);
        }

        /** Len converter */
        inline z3::expr len(const z3::expr &e, const Constants::UInt len) {
            const auto a { e.length() };
            return z3::int2bv(Utils::narrow<z3u>(len), a);
        }

        // Binary

        /** Contains converter */
        inline z3::expr contains(const z3::expr &full, const z3::expr &sub) {
            return full.contains(sub);
        }

        /** PrefixOf converter */
        inline z3::expr prefix_of(const z3::expr &full, const z3::expr &prefix) {
            return z3::prefixof(full, prefix);
        }

        /** SuffixOf converter */
        inline z3::expr suffix_of(const z3::expr &full, const z3::expr &suffix) {
            return z3::suffixof(full, suffix);
        }

        // Ternary

        /** Replace converter */
        inline z3::expr replace(const z3::expr &full, const z3::expr &search,
                                const z3::expr &replacement) {
            return full.replace(search, replacement);
        }

        /** SubString converter */
        inline z3::expr substring(const z3::expr &full, const z3::expr &offset,
                                  const z3::expr &len) {
            const auto a { z3::bv2int(offset, false) };
            const auto b { z3::bv2int(len, false) };
            return full.extract(a, b);
        }

        // Other

        /** IndexOf converter */
        inline z3::expr index_of(const z3::expr &str, const z3::expr &pattern,
                                 const z3::expr &start_index, const Constants::UInt bit_length) {
            const auto a { z3::indexof(str, pattern, start_index) };
            return z3::int2bv(Utils::narrow<z3u>(bit_length), a);
        }

    } // namespace String
} // namespace Backend::Z3::Convert

#endif
