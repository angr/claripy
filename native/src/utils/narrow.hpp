/**
 * @file
 * \ingroup utils
 * @brief This file defines narrow, a function that narrows an integer
 */
#ifndef __UTILS_NARROW_HPP__
#define __UTILS_NARROW_HPP__

#include <type_traits>

namespace Utils {

    /** Narrow X to an Out */
    template <typename Out, typename In> constexpr inline Out narrow(const In in) {
        static_assert(std::is_integral_v<In>, "In must be a primitive");
        static_assert(std::is_integral_v<Out>, "Out must be a primitive");
        return static_cast<Out>(in);
    }

} // namespace Utils

#endif
