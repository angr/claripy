/**
 * @file
 * @brief This file defines Compare mask
 */
#ifndef R_MODE_COMPARE_HPP_
#define R_MODE_COMPARE_HPP_

#include "../utils.hpp"

namespace Mode {
    /** A mask used to define the type of comparisson to be used */
    enum class Compare { Signed = 1, Unsigned = 2, Less = 4, Greater = 8, Eq = 16, Neq = 32 };
} // namespace Mode

// Enable bitmasking
UTILS_BITMASK_ENABLE(Mode::Compare)

namespace Mode {
    /** Return true only if Compare is in a valid state */
    constexpr bool compare_is_valid(const Compare c) {
        namespace B = Utils::BitMask;
        using C = Compare;
        return (B::has(c, C::Signed) ^ B::has(c, C::Unsigned)) &&
               (B::has(c, C::Less) ^ B::has(c, C::Greater)) &&
               (B::has(c, C::Signed) ^ B::has(c, C::Unsigned));
    }
} // namespace Mode

#endif
