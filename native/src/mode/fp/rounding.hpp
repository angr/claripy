/**
 * @file
 * @brief This file defines FP Rounding modes
 */
#ifndef R_MODE_FP_ROUNDING_HPP_
#define R_MODE_FP_ROUNDING_HPP_

#include "rounding.h"

namespace Mode::FP {
    /** FP modes supported by claripy */
    enum class Rounding { MODE_FP_ROUNDING_VALS() };
} // namespace Mode::FP

#endif
