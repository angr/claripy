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

    /** Reverse converter */
    inline Z3::expr reverse(const Z3::expr &e) {
        const auto size { e.size() };
        // Trivial case
        if (size == 8) {
            return e;
        }
        // Error checking
        Utils::affirm<Error::Expression::Operation>(size % 8 == 0,
                                                    "Can't reverse non-byte sized bitvectors");
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
    inline Z3::expr signext(const Z3::expr &e, const unsigned i) { return sext(e, i); }

    /** Zero Extension converter */
    inline Z3::expr zeroext(const Z3::expr &e, const unsigned i) { return zext(e, i); }

    // Binary

    /** Equality comparisson converter */
    inline Z3::expr eq(const Z3::expr &l, const Z3::expr &r) { return l == r; }


    /** Subtraction converter */
    inline Z3::expr sub(const Z3::expr &l, const Z3::expr &r) { return l - r; }


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
    inline Z3::expr add(Constants::CTSC<Z3::expr> arr, const Constants::UInt size) {
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

    namespace FP {}

    namespace String {}

#if 0
	UNARY_CASE(Invert, convert.invert);  // z3 does not suport, concerete only?

	// Binary

	BINARY_TEMPLATE_CASE(Compare, convert.compare, true, true, true);
	BINARY_TEMPLATE_CASE(Compare, convert.compare, true, true, false);
	BINARY_TEMPLATE_CASE(Compare, convert.compare, true, false, true);
	BINARY_TEMPLATE_CASE(Compare, convert.compare, true, false, false);
	BINARY_TEMPLATE_CASE(Compare, convert.compare, false, true, true);
	BINARY_TEMPLATE_CASE(Compare, convert.compare, false, true, false);
	BINARY_TEMPLATE_CASE(Compare, convert.compare, false, false, true);
	BINARY_TEMPLATE_CASE(Compare, convert.compare, false, false, false);

	BINARY_TEMPLATE_CASE(Div, convert.div, true);
	BINARY_TEMPLATE_CASE(Div, convert.div, false);

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
#endif

} // namespace Backend::Z3::Convert

#endif
