/**
 * @file
 * @brief This file defines how the z3 backend converts Claricpp Expressions into Z3 ASTs
 */
#ifndef __BACKEND_Z3_CONVERT_HPP__
#define __BACKEND_Z3_CONVERT_HPP__

#include "z3++.h"

#include "../../op.hpp"


/********************************************************************/
/*                    Claricpp -> Z3 Conversion                     */
/********************************************************************/


namespace Backend::z3::Convert {

    // Unary

    /** Negation converter */
    inline z3::expr neg(const z3::expr &e) { return -e; }

    /** Abs converter */
    inline z3::expr abs(const z3::expr &e) { return z3::abs(e); }

    // IntBinary

    /** Sign Extension converter */
    inline z3::expr signext(const z3::expr &e, const unsigned i) { return sext(e, i); }

    /** Zero Extension converter */
    inline z3::expr zeroext(const z3::expr &e, const unsigned i) { return zext(e, i); }

    // Binary

    /** Equality comparisson converter */
    inline z3::expr eq(const z3::expr &l, const z3::expr &r) { return l == r; }


    /** Subtraction converter */
    inline z3::expr sub(const z3::expr &l, const z3::expr &r) { return l - r; }


    /** Pow converter */
    inline z3::expr pow(const z3::expr &l, const z3::expr &r) { return z3::pow(l, r); }

    // Flat

    // Other

    namespace FP {}

    namespace String {}

#if 0
	UNARY_CASE(Invert, convert.invert);
	UNARY_CASE(Reverse, convert.reverse);

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
#endif

} // namespace Backend::z3::Convert

#endif
