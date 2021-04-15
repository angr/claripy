/**
 * @file
 * @brief This file defines Compare mask
 */
#ifndef __MODE_COMPARE_HPP__
#define __MODE_COMPARE_HPP__

#include "../utils.hpp"

namespace Mode {

    /** A mask used to define the type of comparisson to be used */
    enum class Compare { None = 0, Signed = 1, Less = 2, Eq = 4 };

} // namespace Mode

// Enable bitmasking
ENABLE_AS_BITMASK(Mode::Compare)

#endif
