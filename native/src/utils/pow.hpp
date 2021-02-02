/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::pow
 */
#ifndef __UTILS_POW_HPP__
#define __UTILS_POW_HPP__

#include <type_traits>


namespace Utils {

    /** A compile-time pow function that only allows integral powers
     *  Requires power >= 0
     *  Warning: This should only be used with types that never throw
     */
    template <typename Base>
    constexpr Base pow(const Base base, const unsigned int power) noexcept {
        static_assert(std::is_arithmetic<Base>::value, "Utils::pow Base must be a number");
        if (power == 0) {
            return 1;
        }
        else {
            return base * pow(base, power - 1);
        }
    }

} // namespace Utils

#endif
