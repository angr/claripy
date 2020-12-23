/**
 * @file
 * @brief This file defines Utils::pow
 */
#ifndef __UTILS_POW_HPP__
#define __UTILS_POW_HPP__

#include "../errors/unexpected.hpp"

#include <type_traits>


/** A namespace used for the utils directory */
namespace Utils {

    /** A compile-time pow function that only allows integral powers */
    template <typename Base, typename Power>
    constexpr Base pow(const Base base, const Power power) {
        static_assert(std::is_arithmetic<Base>::value, "Utils::pow Base must be a number");
        static_assert(std::is_integral<Power>::value, "Utils::pow Power must be integral");
        if (power < 0) {
            // This should actually fail compilation here since this is not constexpr
            throw Errors::Unexpected::IncorrectUsage("power must be non-negative");
        }
        else if (power == 0) {
            return 1;
        }
        return base * pow(base, power - 1);
    }

} // namespace Utils

#endif
