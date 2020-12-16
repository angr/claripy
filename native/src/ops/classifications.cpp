/** @file */
#include "classifications.hpp"

#include "../utils/set_join.hpp"


// For brevity
using OpMap = Ops::OpMap;
using OpSet = Ops::OpSet;
using OP = Ops::Operation;

/********************************************************************/
/*                           Expressions                            */
/********************************************************************/

// Define expression operations classifications
const OpSet Ops::Expression::arithmetic = {
    OP::__add__,      OP::__radd__,     OP::__div__,       OP::__rdiv__, OP::__truediv__,
    OP::__rtruediv__, OP::__floordiv__, OP::__rfloordiv__, OP::__mul__,  OP::__rmul__,
    OP::__sub__,      OP::__rsub__,     OP::__pow__,       OP::__rpow__, OP::__mod__,
    OP::__rmod__,     OP::__divmod__,   OP::__rdivmod__,   OP::SDiv,     OP::SMod,
    OP::__neg__,      OP::__pos__,      OP::__abs__,
};

const OpSet Ops::Expression::comparator {
    OP::__eq__, OP::__ne__, OP::__ge__, OP::__le__, OP::__gt__, OP::__lt__,
};

const OpSet Ops::Expression::bitwise {
    OP::__invert__, OP::__or__,     OP::__ror__,     OP::__and__,    OP::__rand__,    OP::__xor__,
    OP::__rxor__,   OP::__lshift__, OP::__rlshift__, OP::__rshift__, OP::__rrshift__,
};

const OpSet Ops::Expression::set {
    OP::union_,
    OP::intersection,
    OP::widen,
};

const OpSet Ops::Expression::operations =
    Utils::set_join(Ops::Expression::arithmetic, Ops::Expression::comparator,
                    Ops::Expression::bitwise, Ops::Expression::set);

/********************************************************************/
/*                           Backend Ops                            */
/********************************************************************/

const OpSet Ops::Backend::comparator {
    OP::SGE, OP::SLE, OP::SGT, OP::SLT, OP::UGE, OP::ULE, OP::UGT, OP::ULT,
};

const OpSet Ops::Backend::bitwise {
    OP::RotateLeft,
    OP::RotateRight,
    OP::LShR,
    OP::Reverse,
};

const OpSet Ops::Backend::boolean { OP::And, OP::Or, OP::Not };

const OpSet Ops::Backend::bitmod { OP::Concat, OP::Extract, OP::SignExt, OP::ZeroExt };

const OpSet Ops::Backend::creation { OP::BoolV, OP::BVV, OP::FPV, OP::StringV };

const OpSet Ops::Backend::symbol_creation { OP::BoolS, OP::BVS, OP::FPS, OP::StringS };

const OpSet Ops::Backend::vsa_creation { OP::TopStridedInterval, OP::StridedInterval, OP::ValueSet,
                                         OP::AbstractLocation };

const OpSet Ops::Backend::other { OP::If };

const OpSet Ops::Backend::arithmetic { OP::SDiv, OP::SMod };

const OpSet Ops::Backend::operations = Utils::set_join(
    Ops::Backend::comparator, Ops::Backend::bitwise, Ops::Backend::boolean, Ops::Backend::bitmod,
    Ops::Backend::creation, Ops::Backend::other, Ops::Backend::arithmetic);

const OpSet Ops::Backend::operations_vsa_compliant = Utils::set_join(
    Ops::Backend::bitwise, Ops::Backend::comparator, Ops::Backend::boolean, Ops::Backend::bitmod);

const OpSet Ops::Backend::operations_all = Utils::set_join(
    Ops::Backend::operations, Ops::Backend::operations_vsa_compliant, Ops::Backend::vsa_creation);

const OpSet Ops::Backend::fp_cmp {
    OP::fpLT, OP::fpLEQ, OP::fpGT, OP::fpGEQ, OP::fpEQ,
};

const OpSet Ops::Backend::fp = Utils::set_join(
    OpSet { OP::FPS, OP::fpToFP, OP::fpToIEEEBV, OP::fpFP, OP::fpToSBV, OP::fpToUBV, OP::fpNeg,
            OP::fpSub, OP::fpAdd, OP::fpMul, OP::fpDiv, OP::fpAbs },
    Ops::Backend::fp_cmp);

const OpSet Ops::Backend::strings = { OP::StrSubstr,   OP::StrReplace,  OP::StrConcat,
                                      OP::StrLen,      OP::StrContains, OP::StrPrefixOf,
                                      OP::StrSuffixOf, OP::StrIndexOf,  OP::StrToInt,
                                      OP::StrIsDigit,  OP::IntToStr };

/********************************************************************/
/*                           Length Ops                             */
/********************************************************************/

const OpSet Ops::Length::same =
    Utils::set_join(Ops::Expression::arithmetic, Ops::Expression::bitwise, Ops::Expression::set,
                    Ops::Backend::bitwise, Ops::Backend::other, OpSet { OP::Reversed });

const OpSet Ops::Length::none =
    Utils::set_join(Ops::Backend::comparator, Ops::Expression::comparator, Ops::Backend::boolean,
                    Ops::Backend::fp_cmp);

const OpSet Ops::Length::change = Ops::Backend::bitmod;

const OpSet Ops::Length::new_ = Ops::Backend::creation;

/********************************************************************/
/*                            Leaf Ops                              */
/********************************************************************/

const OpSet Ops::Leaf::operations = Utils::set_join(
    Ops::Backend::symbol_creation, Ops::Backend::creation, Ops::Backend::vsa_creation);

const OpSet Ops::Leaf::concrete = Ops::Backend::creation;

const OpSet Ops::Leaf::symbolic = Ops::Backend::symbol_creation;

/********************************************************************/
/*                              Other                               */
/********************************************************************/

const OpSet Ops::bin_ops {
    OP::__add__, OP::__radd__, OP::__mul__,  OP::__rmul__, OP::__or__,
    OP::__ror__, OP::__and__,  OP::__rand__, OP::__xor__,  OP::__rxor__,
};

const OpSet Ops::not_invertible {
    OP::Identical,
    OP::union_,
};

const OpSet Ops::reverse_distributable {
    OP::widen,   OP::union_,  OP::intersection, OP::__invert__, OP::__or__,
    OP::__ror__, OP::__and__, OP::__rand__,     OP::__xor__,    OP::__rxor__,
};

const OpSet Ops::commutative = { OP::__and__, OP::__or__, OP::__xor__, OP::__add__,
                                 OP::__mul__, OP::And,    OP::Or };

/********************************************************************/
/*                              Maps                                */
/********************************************************************/

const OpMap Ops::Maps::opposites = {
    { OP::__add__, OP::__radd__ },
    { OP::__radd__, OP::__add__ },
    { OP::__div__, OP::__rdiv__ },
    { OP::__rdiv__, OP::__div__ },
    { OP::__truediv__, OP::__rtruediv__ },
    { OP::__rtruediv__, OP::__truediv__ },
    { OP::__floordiv__, OP::__rfloordiv__ },
    { OP::__rfloordiv__, OP::__floordiv__ },
    { OP::__mul__, OP::__rmul__ },
    { OP::__rmul__, OP::__mul__ },
    { OP::__sub__, OP::__rsub__ },
    { OP::__rsub__, OP::__sub__ },
    { OP::__pow__, OP::__rpow__ },
    { OP::__rpow__, OP::__pow__ },
    { OP::__mod__, OP::__rmod__ },
    { OP::__rmod__, OP::__mod__ },
    { OP::__divmod__, OP::__rdivmod__ },
    { OP::__rdivmod__, OP::__divmod__ },
    { OP::__eq__, OP::__eq__ },
    { OP::__ne__, OP::__ne__ },
    { OP::__ge__, OP::__le__ },
    { OP::__le__, OP::__ge__ },
    { OP::__gt__, OP::__lt__ },
    { OP::__lt__, OP::__gt__ },
    { OP::ULT, OP::UGT },
    { OP::UGT, OP::ULT },
    { OP::ULE, OP::UGE },
    { OP::UGE, OP::ULE },
    { OP::SLT, OP::SGT },
    { OP::SGT, OP::SLT },
    { OP::SLE, OP::SGE },
    { OP::SGE, OP::SLE },
    { OP::__or__, OP::__ror__ },
    { OP::__ror__, OP::__or__ },
    { OP::__and__, OP::__rand__ },
    { OP::__rand__, OP::__and__ },
    { OP::__xor__, OP::__rxor__ },
    { OP::__rxor__, OP::__xor__ },
    { OP::__lshift__, OP::__rlshift__ },
    { OP::__rlshift__, OP::__lshift__ },
    { OP::__rshift__, OP::__rrshift__ },
    { OP::__rrshift__, OP::__rshift__ },
};

const OpMap Ops::Maps::reversed {
    { OP::__radd__, OP::__add__ },
    { OP::__rand__, OP::__and__ },
    { OP::__rdiv__, OP::__div__ },
    { OP::__rdivmod__, OP::__divmod__ },
    { OP::__rfloordiv__, OP::__floordiv__ },
    { OP::__rlshift__, OP::__lshift__ },
    { OP::__rmod__, OP::__mod__ },
    { OP::__rmul__, OP::__mul__ },
    { OP::__ror__, OP::__or__ },
    { OP::__rpow__, OP::__pow__ },
    { OP::__rrshift__, OP::__rshift__ },
    { OP::__rsub__, OP::__sub__ },
    { OP::__rtruediv__, OP::__truediv__ },
    { OP::__rxor__, OP::__xor__ },
};

const OpMap Ops::Maps::inverse {
    { OP::__eq__, OP::__ne__ }, { OP::__ne__, OP::__eq__ }, { OP::__gt__, OP::__le__ },
    { OP::__lt__, OP::__ge__ }, { OP::__ge__, OP::__lt__ }, { OP::__le__, OP::__gt__ },
    { OP::ULT, OP::UGE },       { OP::UGE, OP::ULT },       { OP::UGT, OP::ULE },
    { OP::ULE, OP::UGT },       { OP::SLT, OP::SGE },       { OP::SGE, OP::SLT },
    { OP::SLE, OP::SGT },       { OP::SGT, OP::SLE },
};

/********************************************************************/
/*                              Infix                               */
/********************************************************************/

const std::map<OP, const char *const> Ops::infix {
    { OP::__add__, "+" },
    { OP::__sub__, "-" },
    { OP::__mul__, "*" },
    { OP::__div__, "/" },
    { OP::__floordiv__, "/" },
    { OP::__truediv__, "/" }, // the raw / operator should use integral semantics on bitvectors
    { OP::__pow__, "**" },
    { OP::__mod__, "%" },
    { OP::__eq__, "==" },
    { OP::__ne__, "!=" },
    { OP::__ge__, ">=" },
    { OP::__le__, "<=" },
    { OP::__gt__, ">" },
    { OP::__lt__, "<" },
    { OP::UGE, ">=" },
    { OP::ULE, "<=" },
    { OP::UGT, ">" },
    { OP::ULT, "<" },
    { OP::SGE, ">=s" },
    { OP::SLE, "<=s" },
    { OP::SGT, ">s" },
    { OP::SLT, "<s" },
    { OP::SDiv, "/s" },
    { OP::SMod, "%s" },
    { OP::__or__, "|" },
    { OP::__and__, "&" },
    { OP::__xor__, "^" },
    { OP::__lshift__, "<<" },
    { OP::__rshift__, ">>" },
    { OP::And, "&&" },
    { OP::Or, "||" },
    { OP::Concat, ".." },
};
