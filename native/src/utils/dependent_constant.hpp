/**
 * @file
 * \ingroup utils
 * @brief This file defines type-dependent constants
 */
#ifndef __UTILS_DEPENDENTCONSTANT_HPP__
#define __UTILS_DEPENDENTCONSTANT_HPP__

#include "macros.hpp"


/** A local macro that defines dependent constant types that depend on a METATYPE */
#define DEPCONST(METATYPE)                                                                        \
    /** A dependent constant type                                                                 \
     *  Because templates are not evaluated until use, this can safely be placed                  \
     *  within a constexpr conditional static_assert without instantly trigging an assertion      \
     *  failure. Instead, the static_assert will only fail if the line of code is reached         \
     *  as until that point constant<bool, false, T> is an unevaluated expression, for example.   \
     *  This also has the nice side effect that, if a static_assert fails, the compiler will      \
     *  likely print out the passed types which can help with debugging                           \
     */                                                                                           \
    template <typename T, T value, METATYPE...> inline const constexpr T constant { value };      \
                                                                                                  \
    /** A dependent id variable */                                                                \
    template <auto value> inline const constexpr auto id { value };                               \
                                                                                                  \
    /* Abbreviations */                                                                           \
                                                                                                  \
    /** A dependent boolean */                                                                    \
    template <bool Value, METATYPE... _> UTILS_ICCBOOL boolean { constant<bool, Value, _...> };   \
                                                                                                  \
    /** A dependent false boolean */                                                              \
    template <METATYPE... _> UTILS_ICCBOOL false_ { boolean<false, _...> };                       \
                                                                                                  \
    /** A dependent true boolean */                                                               \
    template <METATYPE... _> UTILS_ICCBOOL true_ { boolean<true, _...> };

// Type dependent constants
namespace Utils::TD {
    DEPCONST(typename)
} // namespace Utils::TD

// Constant dependent constants
namespace Utils::CD {
    DEPCONST(auto)
} // namespace Utils::CD

// Cleanup
#undef DEPCONST

#endif
