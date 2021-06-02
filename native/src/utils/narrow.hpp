/**
 * @file
 * \ingroup utils
 * @brief This file defines narrow, a function that narrows an integer
 */
#ifndef R_UTILS_NARROW_HPP_
#define R_UTILS_NARROW_HPP_

#include <type_traits>

namespace Utils {

    /** Narrow X to an Out */
    template <typename Out, typename In> constexpr Out narrow(const In in) noexcept {
        static_assert(std::is_integral_v<In>, "In must be a primitive");
        static_assert(std::is_integral_v<Out>, "Out must be a primitive");
        static_assert(std::is_convertible_v<In, Out>, "In must be convertible to Out");
        return static_cast<Out>(in);
    }

} // namespace Utils

#endif
