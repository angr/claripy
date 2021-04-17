/**
 * @file
 * @brief This file defines how the Z3 backend converts Claricpp Expressions into Z3 ASTs
 */
#ifndef __BACKEND_Z3_CONVERT_HPP__
#define __BACKEND_Z3_CONVERT_HPP__

#include "z3++.h"

#include "../../op.hpp"

#include <functional>


/********************************************************************/
/*                    Claricpp -> Z3 Conversion                     */
/********************************************************************/


namespace Backend::Z3::Convert {

    namespace Private {
        /** A thread local context all Z3 exprs should use */
        inline thread_local Z3::context tl_context;
    } // namespace Private

    // Unary

    /** Negation converter */
    inline Z3::expr neg(const Z3::expr &e) { return -e; }

    /** Abs converter */
    inline Z3::expr abs(const Z3::expr &e) { return Z3::abs(e); }

    /** Invert converter */
    inline Z3::expr invert(const Z3::expr &e) { return ~e; }

    /** Reverse converter */
    inline Z3::expr reverse(const Z3::expr &e) {
        const auto size { e.size() };
        // Trivial case
        if (size == 8) {
            return e;
        }
        // Error checking
        using Err = Error::Expression::Operation;
        Utils::affirm<Err>(size % 8 == 0, "Can't reverse non-byte sized bitvectors");
        // Reverse byte by byte
        std::vector<Z3::expr> extracted;
        extracted.reserve(size / 8 + 1);
        for (decltype(size) i = 0; i < size; i += 8) {
            extracted.emplace_back(std::move(extract(i + 7, i, e)));
        }
        // Join bytes
        return concat(extracted);
    }

    // IntBinary

    /** Sign Extension converter */
    inline Z3::expr signext(const Z3::expr &e, const unsigned i) { return Z3::sext(e, i); }

    /** Zero Extension converter */
    inline Z3::expr zeroext(const Z3::expr &e, const unsigned i) { return Z3::zext(e, i); }

    // Binary

    /** Equality comparisson converter */
    inline Z3::expr eq(const Z3::expr &l, const Z3::expr &r) { return l == r; }

    /** Compare converter */
    template <Mode::Compare Mask> inline Z3::expr compare(const Z3::expr &l, const Z3::expr &r) {
        using C = Mode::Compare;
        static_assert(Mode::compare_is_valid(Mask), "Invalid mask mode");
        if constexpr (Utils::has_flags(Mask, C::Signed | C::Less | C::Eq)) {
            return Z3::sle(l, r);
        }
        else if constexpr (Utils::has_flags(Mask, C::Signed | C::Less | C::Neq)) {
            return Z3::slt(l, r);
        }
        else if constexpr (Utils::has_flags(Mask, C::Signed | C::Greater | C::Eq)) {
            return Z3::sge(l, r);
        }
        else if constexpr (Utils::has_flags(Mask, C::Signed | C::Greater | C::Neq)) {
            return Z3::sgt(l, r);
        }
        else if constexpr (Utils::has_flags(Mask, C::Unsigned | C::Less | C::Eq)) {
            return Z3::ult(l, r);
        }
        else if constexpr (Utils::has_flags(Mask, C::Unsigned | C::Less | C::Neq)) {
            return Z3::ult(l, r);
        }
        else if constexpr (Utils::has_flags(Mask, C::Unsigned | C::Greater | C::Eq)) {
            return Z3::uge(l, r);
        }
        else if constexpr (Utils::has_flags(Mask, C::Unsigned | C::Greater | C::Neq)) {
            return Z3::ugt(l, r);
        }
        else {
            static_assert(Utils::CD::false_<Mask>, "Unsupported mask mode");
        }
    }

    /** Subtraction converter */
    inline Z3::expr sub(const Z3::expr &l, const Z3::expr &r) { return l - r; }

    /** Division converter */
    template <bool Signed> Z3::expr div(const Z3::expr &l, const Z3::expr &r) {
        if constexpr (Signed) {
            return l / r;
        }
        else {
            return Z3::udiv(l, r);
        }
    }

    /** Pow converter */
    inline Z3::expr pow(const Z3::expr &l, const Z3::expr &r) { return Z3::pow(l, r); }

    /** Mod converter */
    template <bool Signed> Z3::expr mod(const Z3::expr &l, const Z3::expr &r) {
        if constexpr (Signed) {
            return Z3::smod(l, r);
        }
        else {
            return Z3::mod(l, r);
        }
    }

    /** Shift converter */
    template <Mode::Shift Mask> Z3::expr shift(const Z3::expr &l, const Z3::expr &r) {
        using S = Mode::Shift;
        static_assert(Mode::shift_is_valid(Mask), "Invalid mask mode");
        if constexpr (Utils::has_flags(Mask, C::Arithmetic | C::Left)) {
            return Z3::shl(l, r);
        }
        else if constexpr (Utils::has_flags(Mask, C::Arithmetic | C::Right)) {
            return Z3::shr(l, r);
        }
        else if constexpr (Utils::has_flags(Mask, C::Logical | C::Right)) {
            return Z3::lshr(l, r);
        }
        else {
            static_assert(Utils::CD::false_<Mask>, "Unsupported mask mode");
        }
    }

    /** Rotate converter */
    template <bool Left> Z3::expr rotate(const Z3::expr &l, const Z3::expr &r) {
        // z3's C++ API's rotate functions are different (note the "ext" below)
        using namespace Z3;
        const auto &ctx = l.ctx();
        Z3_ast r { Left ? Z3_mk_ext_rotate_left(ctx, l, r) : Z3_mk_ext_rotate_right(ctx, l, r) : };
        ctx.check_error();
        return expr(l.ctx, std::move(r));
    }


    // TODO
    /* BINARY_CASE(Concat, convert.concat); */


    // Flat

    namespace Private {
        /** Like C++20's version of std::accumulate, except it works with pointers */
        template <typename Fn>
        inline Z3::expr ptr_accumulate(Constants::CTSC<Z3::expr> arr, const Constants::UInt size) {
#ifdef DEBUG
            Utils::affirm<Utils::Error::Unexpected::Size>(
                n >= 2, "n < 2; this probably resulted from an invalid claricpp expression.");
#endif
            Z3::expr ret { Fn(*arr[0], *arr[1]) };
            for (Constants::UInt i = 2; i < size; ++i) {
                ret = std::move(Fn(std::move(ret), *arr[i]));
            }
            return ret;
        }
    } // namespace Private

    /** Add converter */
    inline Z3::expr add(Constants::CTSC<Z3::expr> arr, const Constants::UInt size) {
        return Private::ptr_accumulate<std::plus<Z3::expr>>(arr, size);
    }

    /** Mul converter */
    inline Z3::expr mul(Constants::CTSC<Z3::expr> arr, const Constants::UInt size) {
        return Private::ptr_accumulate<std::multiplies<Z3::expr>>(arr, size);
    }

    /** Or converter */
    inline Z3::expr or_(Constants::CTSC<Z3::expr> arr, const Constants::UInt size) {
        // Note that Z3's bit or auto switched to logical or for booleans
        return Private::ptr_accumulate<std::bit_or<Z3::expr>>(arr, size);
    }

    /** And converter */
    inline Z3::expr and_(Constants::CTSC<Z3::expr> arr, const Constants::UInt size) {
        // Note that Z3's bit and auto switched to logical and for booleans
        return Private::ptr_accumulate<std::bit_and<Z3::expr>>(arr, size);
    }

    /** Xor converter */
    inline Z3::expr xor_(Constants::CTSC<Z3::expr> arr, const Constants::UInt size) {
        return Private::ptr_accumulate<std::bit_xor<Z3::expr>>(arr, size);
    }

    // Other

    /** Extract converter */
    inline Z3::expr extract(const unsigned high, const unsigned low, const Z3::expr &e) {
        return e.extract(high, low);
    }

    /** If converter */
    inline Z3::expr if_(const Z3::expr &cond, const Z3::expr &if_true, const Z3::expr &if_false) {
        return Z3::ite(cond, if_true, if_false);
    }

#if 0
		// TODO: @todo
	case Op::Literal::static_cuid: {
		break; // TODO
	}
	case Op::Symbol::static_cuid: {
		break; // TODO
	}
#endif

    namespace FP {
#if 0
		// TODO: @todo
		UNARY_CASE(FP::ToIEEEBV, convert.fp_to_ieee_bv);
		UNARY_CASE(FP::IsInf, convert.fp_is_inf);
		UNARY_CASE(FP::IsNan, convert.fp_is_nan);

		// Binary

		BINARY_CASE(FP::NE, convert.fp_ne);
#endif
        // Mode Binary

        namespace Private {
            /** Verifes 2 expressions are FPs with the same context */
            inline void assert_are_compatible() {
#if DEBUG
                Z3::check_context(a, b);
                Utils::affirm<Utils::Error::Unexpected::Type>(
                    a.is_fpa() && b.is_fpa(), WHOAMI_WITH_SOURCE " called non-FP ops");
#endif
            }
        }; // namespace Private

/** A local macro used for fp math conversions */
#define FP_ARITH_CONVERT(FN)                                                                      \
    inline Z3::expr add(const Mode::FP mode, const Z3::expr &l, const Z3::expr &r) {              \
        Private::assert_are_compatible();                                                         \
        auto r { Z3::Z3_mk_fpa_add(l.ctx(), mode, l, r) };                                        \
        a.check_error();                                                                          \
        return Z3::expr(a.ctx(), r);                                                              \
    }
        /** FP::Add converter */
        FP_ARITH_CONVERT(add)
        /** FP::Sub converter */
        FP_ARITH_CONVERT(sub)
        /** FP::Mul converter */
        FP_ARITH_CONVERT(mul)
        /** FP::Div converter */
        FP_ARITH_CONVERT(div)

// Cleanup
#undef FP_ARITH_CONVERT

        // Ternary
#if 0
		// TODO: @todo
		TERNARY_CASE(FP::FP, convert.fp_fp)

		// Other

		case Op::FP::ToBV::static_cuid: {
			using To = Constants::CTSC<Op::FP::ToBV>;
			auto ret { std::move(
				convert.extract(static_cast<To>(expr)->mode, *args.back())) };
			args.pop_back();
			return ret;
		}
#endif
    } // namespace FP

    namespace String {

        /** FromInt converter */
        inline Z3::expr from_int(const Z3::expr &e) { return z3::bv2int(e).itos(); }

        /** Unit converter */
        inline Z3::expr unit(const Z3::expr &e) { return e.unit(); }

        // Int Binary

        /** ToInt converter */
        inline Z3::expr to_int(const Z3::expr &e, const unsigned len) {
            const auto a { e.stoi() };
            return Z3::int2bv(a, len);
        }

        /** Len converter */
        inline Z3::expr to_int(const Z3::expr &e, const unsigned len) {
            const auto a { e.length() };
            return Z3::int2bv(a, len);
        }

        // Binary

        /** Contains converter */
        inline Z3::expr contains(const Z3::expr &full, const Z3::expr &sub) {
            return full.contains(sub);
        }

        /** PrefixOf converter */
        inline Z3::expr prefix_of(const Z3::expr &full, const Z3::expr &prefix) {
            return Z3::prefixof(full, prefix);
        }

        /** SuffixOf converter */
        inline Z3::expr suffix_of(const Z3::expr &full, const Z3::expr &suffix) {
            return Z3::suffixof(full, suffix);
        }

        // Ternary

        /** Replace converter */
        inline Z3::expr replace(const Z3::expr &full, const Z3::expr &search,
                                const Z3::expr replacement) {
            return full.replace(search, replacement);
        }

        /** SubString converter */
        inline Z3::expr substring(const Z3::expr &full, const Z3::expr &offset,
                                  const Z3::expr &len) {
            const auto a { z3::bv2int(offset) };
            const auto b { z3::bv2int(len) };
            return full.extract(a, b);
        }

        // Other

        /** IndexOf converter */
        inline Z3::expr index_of(const Z3::expr &str, const Z3::expr &pattern,
                                 const Z3::expr &start_index, const unsigned bit_length) {
            const auto a { z3::indexof(str, pattern, start_index) };
            return Z3::int2bv(a, bit_length);
        }
    } // namespace String

} // namespace Backend::Z3::Convert

#endif
