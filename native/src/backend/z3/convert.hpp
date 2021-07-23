/**
 * @file
 * @brief This file defines how the Z3 backend converts Claricpp Expressions into Z3 ASTs
 */
#ifndef R_BACKEND_Z3_CONVERT_HPP_
#define R_BACKEND_Z3_CONVERT_HPP_

#include "constants.hpp"
#include "width.hpp"

#include "../../op.hpp"


/********************************************************************/
/*                    Claricpp -> Z3 Conversion                     */
/********************************************************************/


namespace Backend::Z3::Convert {

    // Forward declarations
    z3::expr concat(const z3::expr &l, const z3::expr &r);
    z3::expr extract(const Constants::UInt high, const Constants::UInt low, const z3::expr &e);

    namespace Private {

        /** A thread_local reference to tl_ctx for brevity */
        auto &tl_ctx { ::Backend::Z3::Private::tl_ctx };

        /** The size of a float
         *  Note that constexpr may not imply inline here so we are explicit
         */
        static inline constexpr const auto flt_size { 4_ui * BitLength::char_bit };

        /** A function that narrows a Constants::UInt to Z3's unsigned type */
        constexpr auto to_z3u(const Constants::UInt x) { return Utils::narrow<unsigned>(x); }

    } // namespace Private

    // Unary

    /** Negation converter */
    inline z3::expr neg(const z3::expr &e) { return -e; }

    /** Abs converter */
    inline z3::expr abs(const z3::expr &e) { return z3::abs(e); }

    /** Not converter */
    inline z3::expr not_(const z3::expr &e) { return !e; }

    /** Invert converter */
    inline z3::expr invert(const z3::expr &e) { return ~e; }

    /** Reverse converter */
    inline z3::expr reverse(const z3::expr &e) {
        const auto size { e.get_sort().bv_size() };

        // Trivial case
        if (size == C_CHAR_BIT) {
            return e;
        }

        // Error checking
        using Err = Error::Expression::Operation;
        Utils::affirm<Err>(size % C_CHAR_BIT == 0, "Can't reverse non-byte sized bitvectors");

        // Reverse byte by byte
        auto ret { extract(C_CHAR_BIT - 1u, 0u, e) };
        for (Constants::UInt i = C_CHAR_BIT; i < size; i += C_CHAR_BIT) {
            const auto tmp { extract(Private::to_z3u(i + C_CHAR_BIT - 1), Private::to_z3u(i), e) };
            ret = ::Backend::Z3::Convert::concat(ret, tmp);
        }
        return ret;
    }

    // UIntBinary

    /** Sign Extension converter */
    inline z3::expr signext(const z3::expr &e, const Constants::UInt i) {
        return z3::sext(e, Private::to_z3u(i));
    }

    /** Zero Extension converter */
    inline z3::expr zeroext(const z3::expr &e, const Constants::UInt i) {
        return z3::zext(e, Private::to_z3u(i));
    }

    // Binary

    /** Equality comparison converter */
    inline z3::expr eq(const z3::expr &l, const z3::expr &r) { return l == r; }

    /** Not-equals comparison converter */
    inline z3::expr neq(const z3::expr &l, const z3::expr &r) { return l != r; }

    /** Compare converter */
    template <Mode::Compare Mask> inline z3::expr compare(const z3::expr &l, const z3::expr &r) {
        using C = Mode::Compare;
        static_assert(Mode::compare_is_valid(Mask), "Invalid mask mode");
        if constexpr (Utils::BitMask::has(Mask, C::Signed | C::Less | C::Eq)) {
            if (l.is_fpa()) {
                return l <= r;
            }
            else {
                return z3::sle(l, r);
            }
        }
        else if constexpr (Utils::BitMask::has(Mask, C::Signed | C::Less | C::Neq)) {
            if (l.is_fpa()) {
                return l < r;
            }
            else {
                return z3::slt(l, r);
            }
        }
        else if constexpr (Utils::BitMask::has(Mask, C::Signed | C::Greater | C::Eq)) {
            if (l.is_fpa()) {
                return l >= r;
            }
            else {
                return z3::sge(l, r);
            }
        }
        else if constexpr (Utils::BitMask::has(Mask, C::Signed | C::Greater | C::Neq)) {
            if (l.is_fpa()) {
                return l > r;
            }
            else {
                return z3::sgt(l, r);
            }
        }
        else if constexpr (Utils::BitMask::has(Mask, C::Unsigned | C::Less | C::Eq)) {
            return z3::ule(l, r);
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

    /** Mod converter
     *  Note we use rem (because of the difference between C and Python % operators)
     */
    template <bool Signed> z3::expr mod(const z3::expr &l, const z3::expr &r) {
        if constexpr (Signed) {
            return z3::srem(l, r);
        }
        else {
            return z3::urem(l, r);
        }
    }

    /** Shift converter */
    template <Mode::Shift Mask> z3::expr shift(const z3::expr &l, const z3::expr &r) {
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
            static_assert(Utils::CD::false_<Mask>, "Unsupported mask mode");
        }
    }

    /** Rotate converter */
    template <Mode::LR LR> z3::expr rotate(const z3::expr &l, const z3::expr &r) {
        // z3's C++ API's rotate functions are different (note the "ext" below)
        using namespace Z3;
        z3::expr ret { l.ctx(), (LR == Mode::LR::Left ? Z3_mk_ext_rotate_left(l.ctx(), l, r)
                                                      : Z3_mk_ext_rotate_right(l.ctx(), l, r)) };
        l.ctx().check_error();
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
            UTILS_AFFIRM_NOT_NULL_DEBUG(arr[0]);
            UTILS_AFFIRM_NOT_NULL_DEBUG(arr[1]);
#endif
            const FunctorType fn {};
            z3::expr ret { fn(*arr[0], *arr[1]) };
            for (Constants::UInt i { 2 }; i < size; ++i) {
                UTILS_AFFIRM_NOT_NULL_DEBUG(arr[i]);
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
        return e.extract(Private::to_z3u(high), Private::to_z3u(low));
    }

    /** If converter */
    inline z3::expr if_(const z3::expr &cond, const z3::expr &if_true, const z3::expr &if_false) {
        return z3::ite(cond, if_true, if_false);
    }

    /** Literal converter
     *  expr may not be nullptr
     */
    inline z3::expr literal(const Expression::RawPtr expr) {
        UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
        UTILS_AFFIRM_NOT_NULL_DEBUG(expr->op); // Sanity check
        using To = Constants::CTSC<Op::Literal>;
        const auto &data { Utils::checked_static_cast<To>(expr->op.get())->value };
        try {
            switch (data.index()) {
                case 0:
                    UTILS_VARIANT_VERIFY_INDEX_TYPE(data, 0, bool);
                    return Private::tl_ctx.bool_val(std::get<bool>(data));
                case 1:
                    UTILS_VARIANT_VERIFY_INDEX_TYPE(data, 1, std::string);
                    return Private::tl_ctx.string_val(std::get<std::string>(data));
                case 2:
                    UTILS_VARIANT_VERIFY_INDEX_TYPE(data, 2, float);
                    return Private::tl_ctx.fpa_val(std::get<float>(data));
                case 3:
                    UTILS_VARIANT_VERIFY_INDEX_TYPE(data, 3, double);
                    return Private::tl_ctx.fpa_val(std::get<double>(data));
                case 4:
                    UTILS_VARIANT_VERIFY_INDEX_TYPE(data, 4, PyObj::VSPtr);
                    throw Error::Backend::Unsupported(WHOAMI_WITH_SOURCE
                                                      "VSA is not supported by the Z3 backend");
/** A local macro used for consistency */
#define STD_INT(INDEX, TYPE, BL)                                                                  \
    case INDEX:                                                                                   \
        UTILS_VARIANT_VERIFY_INDEX_TYPE(data, INDEX, TYPE);                                       \
        return Private::tl_ctx.bv_val(std::get<TYPE>(data), BL);
                    STD_INT(5, uint8_t, 8);
                    STD_INT(6, uint16_t, 16);
                    STD_INT(7, uint32_t, 32);
                    STD_INT(8, uint64_t, 64);
// Cleanup
#undef STD_INT
                case 9: {
                    UTILS_VARIANT_VERIFY_INDEX_TYPE(data, 9, BigInt);
                    const auto &big { std::get<BigInt>(data) };
                    std::ostringstream s;
                    s << big.value;
                    return Private::tl_ctx.bv_val(s.str().c_str(),
                                                  Private::to_z3u(big.bit_length));
                }
                    // Error handling
                default:
                    throw Utils::Error::Unexpected::NotSupported(
                        WHOAMI_WITH_SOURCE
                        "Unknown variant type in literal op given to z3 backend");
            }
        }
        // Re-emit these exceptions with additional info and wrapped as a Claricpp exception
        catch (const std::bad_variant_access &ex) {
            throw Utils::Error::Unexpected::BadVariantAccess(WHOAMI_WITH_SOURCE, ex.what());
        }
    }

    /** Symbol converter
     *  This saves symbol annotation for later translocation
     *  expr may not be nullptr
     *  @todo remove the hack
     */
    inline z3::expr symbol(const Expression::RawPtr expr, SymAnTransData &satd) {
        UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
        UTILS_AFFIRM_NOT_NULL_DEBUG(expr->op); // Sanity check
        using To = Constants::CTSC<Op::Symbol>;
        const std::string &name { Utils::checked_static_cast<To>(expr->op.get())->name };
        switch (expr->cuid) {
            case Expression::Bool::static_cuid:
                return Private::tl_ctx.bool_const(name.c_str());
            case Expression::String::static_cuid:
                return Private::tl_ctx.string_const(name.c_str());
            case Expression::FP::static_cuid: {
                using FPP = Constants::CTSC<Expression::FP>;
                const auto fpw { (Utils::checked_static_cast<FPP>(expr)->bit_length ==
                                  Private::flt_size)
                                     ? Mode::FP::flt
                                     : Mode::FP::dbl };
                return Private::tl_ctx.fpa_const(name.c_str(), fpw.exp, fpw.mantissa);
            }
            case Expression::BV::static_cuid: {
                using BVP = Constants::CTSC<Expression::BV>;
#ifdef DEBUG
                Utils::affirm<Utils::Error::Unexpected::Unknown>(
                    Factory::Private::gcache<Expression::Base>().find(expr->hash) != nullptr,
                    WHOAMI_WITH_SOURCE "cache lookup failed for existing object");
#endif
                // Store annotations for translocation
                // We do this even if it is nullptr in case an old pointer exists
                satd.emplace(name, expr->annotations);
                // Return the converted constant
                const Constants::UInt bit_length {
                    Utils::checked_static_cast<BVP>(expr)->bit_length
                };
                return Private::tl_ctx.bv_const(name.c_str(), Private::to_z3u(bit_length));
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

        /** ToIEEEBV converter */
        inline z3::expr to_ieee_bv(const z3::expr &e) { return e.mk_to_ieee_bv(); }

        // Mode Binary

        namespace Private {

            /** Verifies 2 expressions are FPs with the same context */
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
            constexpr z3::rounding_mode to_z3_rm(const Mode::FP::Rounding mode) {
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
                        throw Utils::Error::Unexpected::NotSupported(
                            WHOAMI_WITH_SOURCE "Unable to map Mode::FP::Rounding ", mode,
                            " to z3::rounding_mode");
                };
            }

            /** An alias to to_z3u */
            const constexpr auto to_z3u = ::Backend::Z3::Convert::Private::to_z3u;

        }; // namespace Private

        /** FP::Add converter */
        inline z3::expr add(const Mode::FP::Rounding mode, const z3::expr &l, const z3::expr &r) {
            l.ctx().set_rounding_mode(Private::to_z3_rm(mode));
            return l + r;
        }

        /** FP::Sub converter */
        inline z3::expr sub(const Mode::FP::Rounding mode, const z3::expr &l, const z3::expr &r) {
            l.ctx().set_rounding_mode(Private::to_z3_rm(mode));
            return l - r;
        }

        /** FP::Mul converter */
        inline z3::expr mul(const Mode::FP::Rounding mode, const z3::expr &l, const z3::expr &r) {
            l.ctx().set_rounding_mode(Private::to_z3_rm(mode));
            return l * r;
        }

        /** FP::Div converter */
        inline z3::expr div(const Mode::FP::Rounding mode, const z3::expr &l, const z3::expr &r) {
            l.ctx().set_rounding_mode(Private::to_z3_rm(mode));
            return l / r;
        }

        // Other

        /** FP::ToBV converter */
        template <bool Signed>
        inline z3::expr to_bv(const Mode::FP::Rounding mode, const z3::expr &e,
                              const Constants::UInt bit_length) {
            e.ctx().set_rounding_mode(Private::to_z3_rm(mode));
            if constexpr (Signed) {
                return z3::fpa_to_sbv(e, Private::to_z3u(bit_length));
            }
            else {
                return z3::fpa_to_ubv(e, Private::to_z3u(bit_length));
            }
        }

        /** FP::FromFP converter */
        inline z3::expr from_fp(const Mode::FP::Rounding mode, const z3::expr &e,
                                const Mode::FP::Width &width) {
            e.ctx().set_rounding_mode(Private::to_z3_rm(mode));
            return z3::fpa_to_fpa(e, unsafe_fp_width_to_z3_sort(width));
        }

        /** FP::From2sComplementBV converter */
        template <bool Signed>
        inline z3::expr from_2s_complement_bv(const Mode::FP::Rounding mode, const z3::expr &e,
                                              const Mode::FP::Width &width) {
            e.ctx().set_rounding_mode(Private::to_z3_rm(mode));
            if constexpr (Signed) {
                return z3::sbv_to_fpa(e, unsafe_fp_width_to_z3_sort(width));
            }
            else {
                return z3::ubv_to_fpa(e, unsafe_fp_width_to_z3_sort(width));
            }
        }

        /** FP::FromNot2sComplementBV converter */
        inline z3::expr from_not_2s_complement_bv(const z3::expr &e,
                                                  const Mode::FP::Width &width) {
            return e.mk_from_ieee_bv(unsafe_fp_width_to_z3_sort(width));
        }

    } // namespace FP

    namespace String {

        /** FromInt converter
         *  \todo double check
         */
        inline z3::expr from_int(const z3::expr &e) { return z3::bv2int(e, false).itos(); }

        // Int Binary

        /** ToInt converter */
        inline z3::expr to_int(const z3::expr &e, const Constants::UInt len) {
            const auto a { e.stoi() };
            return z3::int2bv(Private::to_z3u(len), a);
        }

        /** Len converter */
        inline z3::expr len(const z3::expr &e, const Constants::UInt len) {
            const auto a { e.length() };
            return z3::int2bv(Private::to_z3u(len), a);
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
            return z3::int2bv(Private::to_z3u(bit_length), a);
        }

    } // namespace String

} // namespace Backend::Z3::Convert

#endif
