/**
 * @file
 * \ingroup utils
 * @brief This file defines type-dependent constants
 */
#ifndef __UTILS_TYPEDEPENDENTCONSTANT_HPP__
#define __UTILS_TYPEDEPENDENTCONSTANT_HPP__


namespace Utils::TD {

    /** A type-dependent constant type
     *  Because templates are not evaluated until use, this can safely be placed
     *  within a constexpr conditional static_assert without instantly trigging an assertion
     *  failure. Instead, the static_assert will only fail if the line of code is reached
     *  as until that point constant<bool, false, T> is an unevaluated expression, for example.
     *  This also has the nice side effect that, if a static_assert fails, the compiler will
     *  likely print out the passed types which can help with debugging
     */
    template <typename T, T value, typename...> inline const constexpr T constant { value };

    // Abbreviations

    /** A type dependent boolean */
    template <bool Value, typename... _> UTILS_ICCBOOL boolean { constant<bool, Value, _...> };

    /** A type dependent false boolean */
    template <typename... _> UTILS_ICCBOOL false_ { boolean<false, _...> };

    /** A type dependent true boolean */
    template <typename... _> UTILS_ICCBOOL true_ { boolean<true, _...> };

} // namespace Utils::TD

#endif
