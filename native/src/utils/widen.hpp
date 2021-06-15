/**
 * @file
 * \ingroup utils
 * @brief This file defines widen, a function that safely widens an integer
 */
#ifndef R_UTILS_WIDEN_HPP_
#define R_UTILS_WIDEN_HPP_

#include <type_traits>


namespace Utils {

    /** Narrow X to an Out */
    template <typename Out, typename In, bool AllowSignChange = false>
    constexpr Out widen(const In in) noexcept {
        static_assert(std::is_integral_v<In>, "In must be a primitive");
        static_assert(std::is_integral_v<Out>, "Out must be a primitive");
        static_assert(std::is_convertible_v<In, Out>, "In must be convertible to Out");
        static_assert(sizeof(Out) > sizeof(In), "Nothing to widen");
        static_assert(std::is_signed_v<In> == std::is_signed_v<Out>, "Will not change sign");
        return static_cast<In>(in);
    }

} // namespace Utils

#endif
