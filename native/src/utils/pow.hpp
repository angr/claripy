/**
 * @file
 * @brief This file defines Utils::pow
 */
#ifndef __UTILS_POW_HPP__
#define __UTILS_POW_HPP__

#include "affirm.hpp"
#include "error.hpp"


namespace Utils {

    /** A compile-time pow function that only allows integral powers
     *  Requires power >= 0
     */
    template <typename Base, typename Power>
    constexpr Base pow(const Base base, const Power power) {
        static_assert(std::is_arithmetic<Base>::value, "Utils::pow Base must be a number");
        static_assert(std::is_integral<Power>::value, "Utils::pow Power must be integral");
        affirm<Error::Unexpected::IncorrectUsage>(power >= 0,
                                                  "Utils::pow: power must be non-negative");
        if (power == 0) {
            return 1;
        }
        else {
            return base * pow(base, power - 1);
        }
    }

} // namespace Utils

#endif
