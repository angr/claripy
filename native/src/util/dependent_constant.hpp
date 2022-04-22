/**
 * @file
 * \ingroup util
 * @brief This file defines type-dependent constants
 */
#ifndef R_SRC_UTIL_DEPENDENTCONSTANT_HPP_
#define R_SRC_UTIL_DEPENDENTCONSTANT_HPP_

#include "macros.hpp"


// A local macro that defines dependent constant types that depend on a METATYPE
// Because templates are not evaluated until use, these can safely be placed
// within a constexpr conditional static_assert without instantly triggering an assertion
// failure. Instead, the static_assert will only fail if the line of code is reached
// as until that point constant<bool, false, T> is an unevaluated expr, for example.
// This also has the nice side effect that, if a static_assert fails, the compiler will
// likely print out the passed types which can help with debugging
#define M_DEPCONST(METATYPE)                                                                       \
    /** A dependent constant variable */                                                           \
    template <typename T, T value, METATYPE...> inline const constexpr T constant { value };       \
                                                                                                   \
    /** A dependent id variable */                                                                 \
    template <auto value> inline const constexpr auto id { value };                                \
                                                                                                   \
    /* Abbreviations */                                                                            \
                                                                                                   \
    /** A dependent boolean */                                                                     \
    template <bool Value, METATYPE... _> UTIL_ICCBOOL boolean { constant<bool, Value, _...> };     \
                                                                                                   \
    /** A dependent false boolean */                                                               \
    template <METATYPE... _> UTIL_ICCBOOL false_ { boolean<false, _...> };                         \
                                                                                                   \
    /** A dependent true boolean */                                                                \
    template <METATYPE... _> UTIL_ICCBOOL true_ { boolean<true, _...> };

// Type dependent constants
namespace Util::TD {
    M_DEPCONST(typename);
} // namespace Util::TD

// Constant dependent constants
namespace Util::CD {
    M_DEPCONST(auto);
} // namespace Util::CD

#undef M_DEPCONST

#endif
