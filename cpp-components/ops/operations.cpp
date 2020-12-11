#include "operations.hpp"
#include "../utils/set_join.hpp"

// For brevity
using OpSet=Ops::OpSet;
using OP=Ops::Operations;

/********************************************************************/
/*                           Expressions                            */
/********************************************************************/

// Define expression operations classifications
const OpSet Ops::Expression::arithmetic = {
	OP::__add__,
	OP::__radd__,
	OP::__div__,
	OP::__rdiv__,
	OP::__truediv__,
	OP::__rtruediv__,
	OP::__floordiv__,
	OP::__rfloordiv__,
	OP::__mul__,
	OP::__rmul__,
	OP::__sub__,
	OP::__rsub__,
	OP::__pow__,
	OP::__rpow__,
	OP::__mod__,
	OP::__rmod__,
	OP::__divmod__,
	OP::__rdivmod__,
	OP::SDiv,
	OP::SMod,
	OP::__neg__,
	OP::__pos__,
	OP::__abs__,
};

const OpSet Ops::Expression::comparator {
	OP::__eq__,
	OP::__ne__,
	OP::__ge__,
	OP::__le__,
	OP::__gt__,
	OP::__lt__,
};

const OpSet Ops::Expression::bitwise {
	OP::__invert__,
	OP::__or__,
	OP::__ror__,
	OP::__and__,
	OP::__rand__,
	OP::__xor__,
	OP::__rxor__,
	OP::__lshift__,
	OP::__rlshift__,
	OP::__rshift__,
	OP::__rrshift__,
};

const OpSet Ops::Expression::set {
	OP::Union,
	OP::intersection,
	OP::widen,
};

const OpSet Ops::Expression::operations = Utils::set_join<Operations>(
	Ops::Expression::arithmetic,
	Ops::Expression::comparator,
	Ops::Expression::bitwise,
	Ops::Expression::set
);

/********************************************************************/
/*                            Binary Ops                            */
/********************************************************************/

const OpSet Ops::bin_ops {
	OP::__add__,
	OP::__radd__,
	OP::__mul__,
	OP::__rmul__,
	OP::__or__,
	OP::__ror__,
	OP::__and__,
	OP::__rand__,
	OP::__xor__,
	OP::__rxor__,
};

/********************************************************************/
/*                           Backend Ops                            */
/********************************************************************/

const OpSet Ops::Backend::comparator {
	OP::SGE,
	OP::SLE,
	OP::SGT,
	OP::SLT,
	OP::UGE,
	OP::ULE,
	OP::UGT,
	OP::ULT,
};

const OpSet Ops::Backend::bitwise {
	OP::RotateLeft,
	OP::RotateRight,
	OP::LShR,
	OP::Reverse,
};

const OpSet Ops::Backend::boolean {
	OP::And,
	OP::Or,
	OP::Not
};

const OpSet Ops::Backend::bitmod {
	OP::Concat,
	OP::Extract,
	OP::SignExt,
	OP::ZeroExt
};

const OpSet Ops::Backend::creation {
	OP::BoolV,
	OP::BVV,
	OP::FPV,
	OP::StringV
};

const OpSet Ops::Backend::symbol_creation {
	OP::BoolS,
	OP::BVS,
	OP::FPS,
	OP::StringS
};

const OpSet Ops::Backend::vsa_creation {
	OP::TopStridedInterval,
	OP::StridedInterval,
	OP::ValueSet,
	OP::AbstractLocation
};

const OpSet Ops::Backend::other {
	OP::If
};

const OpSet Ops::Backend::arithmetic {
	OP::SDiv,
	OP::SMod
};

const OpSet Ops::Backend::operations = Utils::set_join<Operations>(
	Ops::Backend::comparator,
	Ops::Backend::bitwise,
	Ops::Backend::boolean,
	Ops::Backend::bitmod,
	Ops::Backend::creation,
	Ops::Backend::other,
	Ops::Backend::arithmetic
);

const OpSet Ops::Backend::operations_vsa_compliant = Utils::set_join<Operations>(
	Ops::Backend::bitwise,
	Ops::Backend::comparator,
	Ops::Backend::boolean,
	Ops::Backend::bitmod
);

const OpSet Ops::Backend::operations_all = Utils::set_join<Operations>(
	Ops::Backend::operations,
	Ops::Backend::operations_vsa_compliant,
	Ops::Backend::vsa_creation
);

const OpSet Ops::Backend::fp_cmp {
    OP::fpLT,
	OP::fpLEQ,
	OP::fpGT,
	OP::fpGEQ,
	OP::fpEQ,
};

const OpSet Ops::Backend::fp = Utils::set_join<Operations>(
	OpSet {
		OP::FPS,
		OP::fpToFP,
		OP::fpToIEEEBV,
		OP::fpFP,
		OP::fpToSBV,
		OP::fpToUBV,
		OP::fpNeg,
		OP::fpSub,
		OP::fpAdd,
		OP::fpMul,
		OP::fpDiv,
		OP::fpAbs
	},
	Ops::Backend::fp_cmp
);

const OpSet Ops::Backend::strings = {
    OP::StrSubstr,
	OP::StrReplace,
	OP::StrConcat,
	OP::StrLen,
	OP::StrContains,
    OP::StrPrefixOf,
	OP::StrSuffixOf,
	OP::StrIndexOf,
	OP::StrToInt,
	OP::StrIsDigit,
    OP::IntToStr
};
