/** @file */
#include "classifications.hpp"

#include "../utils.hpp"


// For brevity
using OpMap = Op::OpMap;
using OpSet = Op::OpSet;
using OP = Op::Operation;

/********************************************************************/
/*                           Expressions                            */
/********************************************************************/

const OpSet Op::Expression::arithmetic = {
    OP::__add__,      OP::__radd__,     OP::__div__,       OP::__rdiv__, OP::__truediv__,
    OP::__rtruediv__, OP::__floordiv__, OP::__rfloordiv__, OP::__mul__,  OP::__rmul__,
    OP::__sub__,      OP::__rsub__,     OP::__pow__,       OP::__rpow__, OP::__mod__,
    OP::__rmod__,     OP::__divmod__,   OP::__rdivmod__,   OP::SDiv,     OP::SMod,
    OP::__neg__,      OP::__pos__,      OP::__abs__,
};

const OpSet Op::Expression::comparator {
    OP::__eq__, OP::__ne__, OP::__ge__, OP::__le__, OP::__gt__, OP::__lt__,
};

const OpSet Op::Expression::bitwise {
    OP::__invert__, OP::__or__,     OP::__ror__,     OP::__and__,    OP::__rand__,    OP::__xor__,
    OP::__rxor__,   OP::__lshift__, OP::__rlshift__, OP::__rshift__, OP::__rrshift__,
};

const OpSet Op::Expression::set {
    OP::union_,
    OP::intersection,
    OP::widen,
};

const OpSet Op::Expression::operations =
    Utils::set_join(Op::Expression::arithmetic, Op::Expression::comparator,
                    Op::Expression::bitwise, Op::Expression::set);

/********************************************************************/
/*                           Backend Op                            */
/********************************************************************/

const OpSet Op::Backend::comparator {
    OP::SGE, OP::SLE, OP::SGT, OP::SLT, OP::UGE, OP::ULE, OP::UGT, OP::ULT,
};

const OpSet Op::Backend::bitwise {
    OP::RotateLeft,
    OP::RotateRight,
    OP::LShR,
    OP::Reverse,
};

const OpSet Op::Backend::boolean { OP::And, OP::Or, OP::Not };

const OpSet Op::Backend::bitmod { OP::Concat, OP::Extract, OP::SignExt, OP::ZeroExt };

const OpSet Op::Backend::creation { OP::BoolV, OP::BVV, OP::FPV, OP::StringV };

const OpSet Op::Backend::symbol_creation { OP::BoolS, OP::BVS, OP::FPS, OP::StringS };

const OpSet Op::Backend::vsa_creation { OP::TopStridedInterval, OP::StridedInterval, OP::ValueSet,
                                        OP::AbstractLocation };

const OpSet Op::Backend::other { OP::If };

const OpSet Op::Backend::arithmetic { OP::SDiv, OP::SMod };

const OpSet Op::Backend::operations = Utils::set_join(
    Op::Backend::comparator, Op::Backend::bitwise, Op::Backend::boolean, Op::Backend::bitmod,
    Op::Backend::creation, Op::Backend::other, Op::Backend::arithmetic);

const OpSet Op::Backend::operations_vsa_compliant = Utils::set_join(
    Op::Backend::bitwise, Op::Backend::comparator, Op::Backend::boolean, Op::Backend::bitmod);

const OpSet Op::Backend::operations_all = Utils::set_join(
    Op::Backend::operations, Op::Backend::operations_vsa_compliant, Op::Backend::vsa_creation);

const OpSet Op::Backend::fp_cmp {
    OP::fpLT, OP::fpLEQ, OP::fpGT, OP::fpGEQ, OP::fpEQ,
};

const OpSet Op::Backend::fp = Utils::set_join(
    OpSet { OP::FPS, OP::fpToFP, OP::fpToIEEEBV, OP::fpFP, OP::fpToSBV, OP::fpToUBV, OP::fpNeg,
            OP::fpSub, OP::fpAdd, OP::fpMul, OP::fpDiv, OP::fpAbs },
    Op::Backend::fp_cmp);

const OpSet Op::Backend::strings = { OP::StrSubstr,   OP::StrReplace,  OP::StrConcat,
                                     OP::StrLen,      OP::StrContains, OP::StrPrefixOf,
                                     OP::StrSuffixOf, OP::StrIndexOf,  OP::StrToInt,
                                     OP::StrIsDigit,  OP::IntToStr };

/********************************************************************/
/*                           Length Op                             */
/********************************************************************/

const OpSet Op::Length::same =
    Utils::set_join(Op::Expression::arithmetic, Op::Expression::bitwise, Op::Expression::set,
                    Op::Backend::bitwise, Op::Backend::other, OpSet { OP::Reversed });

const OpSet Op::Length::none = Utils::set_join(Op::Backend::comparator, Op::Expression::comparator,
                                               Op::Backend::boolean, Op::Backend::fp_cmp);

const OpSet Op::Length::change = Op::Backend::bitmod;

const OpSet Op::Length::new_ = Op::Backend::creation;

/********************************************************************/
/*                            Leaf Op                              */
/********************************************************************/

const OpSet Op::Leaf::operations = Utils::set_join(
    Op::Backend::symbol_creation, Op::Backend::creation, Op::Backend::vsa_creation);

const OpSet Op::Leaf::concrete = Op::Backend::creation;

const OpSet Op::Leaf::symbolic = Op::Backend::symbol_creation;

/********************************************************************/
/*                              Other                               */
/********************************************************************/

const OpSet Op::bin_ops {
    OP::__add__, OP::__radd__, OP::__mul__,  OP::__rmul__, OP::__or__,
    OP::__ror__, OP::__and__,  OP::__rand__, OP::__xor__,  OP::__rxor__,
};

const OpSet Op::not_invertible {
    OP::Identical,
    OP::union_,
};

const OpSet Op::reverse_distributable {
    OP::widen,   OP::union_,  OP::intersection, OP::__invert__, OP::__or__,
    OP::__ror__, OP::__and__, OP::__rand__,     OP::__xor__,    OP::__rxor__,
};

const OpSet Op::commutative = { OP::__and__, OP::__or__, OP::__xor__, OP::__add__,
                                OP::__mul__, OP::And,    OP::Or };

/********************************************************************/
/*                              Maps                                */
/********************************************************************/

const OpMap Op::Maps::opposites = {
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

const OpMap Op::Maps::reversed {
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

const OpMap Op::Maps::inverse {
    { OP::__eq__, OP::__ne__ }, { OP::__ne__, OP::__eq__ }, { OP::__gt__, OP::__le__ },
    { OP::__lt__, OP::__ge__ }, { OP::__ge__, OP::__lt__ }, { OP::__le__, OP::__gt__ },
    { OP::ULT, OP::UGE },       { OP::UGE, OP::ULT },       { OP::UGT, OP::ULE },
    { OP::ULE, OP::UGT },       { OP::SLT, OP::SGE },       { OP::SGE, OP::SLT },
    { OP::SLE, OP::SGT },       { OP::SGT, OP::SLE },
};

/********************************************************************/
/*                              Infix                               */
/********************************************************************/

const std::map<OP, Constants::CCSC> Op::infix {
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
