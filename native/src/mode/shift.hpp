/**
 * @file
 * @brief This file defines Shift mask
 */
#ifndef R_MODE_SHIFT_HPP_
#define R_MODE_SHIFT_HPP_

#include "../utils.hpp"

namespace Mode {
    /** A mask used to define the type of comparisson to be used */
    enum class Shift { Arithmetic = 1, Logical = 2, Left = 4, Right = 8 };
} // namespace Mode

// Enable bitmasking
UTILS_BITMASK_ENABLE(Mode::Shift)

namespace Mode {
    /** Return true only if Compare is in a valid state */
    constexpr bool shift_is_valid(const Shift c) {
        namespace B = Utils::BitMask;
        using S = Shift;
        const bool logic { B::has(c, S::Logical) };
        const bool left { B::has(c, S::Left) };
        return (logic ^ B::has(c, S::Arithmetic)) // Logical or Arithmetic
            && (left ^ B::has(c, S::Right))       // Left or right
            && !(left && logic);                  // Not left and logical
    }
} // namespace Mode

#endif
