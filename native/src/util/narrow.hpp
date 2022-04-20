/**
 * @file
 * \ingroup util
 * @brief This file defines narrow, a function that narrows an integer
 */
#ifndef R_SRC_UTIL_NARROW_HPP_
#define R_SRC_UTIL_NARROW_HPP_

#include <type_traits>


namespace Util {

    /** Narrow X to an Out */
    template <typename Out, bool AllowSignChange = false, typename In = void>
    constexpr inline Out narrow(const In in) noexcept {
        static_assert(std::is_integral_v<In>, "In must be a primitive");
        static_assert(std::is_integral_v<Out>, "Out must be a primitive");
        static_assert(std::is_convertible_v<In, Out>, "In must be convertible to Out");
        static_assert(sizeof(Out) < sizeof(In), "Nothing to narrow");
        static_assert(AllowSignChange || std::is_signed_v<In> == std::is_signed_v<Out>,
                      "Will not change sign");
        return static_cast<Out>(in);
    }

} // namespace Util

#endif
