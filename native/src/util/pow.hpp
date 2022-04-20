/**
 * @file
 * \ingroup util
 * @brief This file defines Util::pow
 */
#ifndef R_SRC_UTIL_POW_HPP_
#define R_SRC_UTIL_POW_HPP_

#include <cstdint>
#include <type_traits>


namespace Util {

    /** A compile-time pow function that only allows integral powers
     *  Requires power >= 0
     *  Warning: This should only be used with types that never throw
     */
    template <typename Base> constexpr Base pow(const Base base, const uint32_t power) noexcept {
        static_assert(std::is_arithmetic<Base>::value, "Util::pow Base must be a number");
        if (power == 0) {
            return 1;
        }
        else {
            return base * pow(base, power - 1);
        }
    }

} // namespace Util

#endif
