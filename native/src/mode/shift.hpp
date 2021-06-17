/**
 * @file
 * @brief This file defines Shift mask
 */
#ifndef R_MODE_SHIFT_HPP_
#define R_MODE_SHIFT_HPP_

#include "../utils.hpp"

namespace Mode {

    /** A mask used to define the type of comparisson to be used */
    enum class Shift { Left, LogicalRight, ArithmeticRight };

} // namespace Mode

#endif
