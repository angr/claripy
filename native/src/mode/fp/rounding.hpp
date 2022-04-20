/**
 * @file
 * @brief This file defines FP Rounding modes
 */
#ifndef R_SRC_MODE_FP_ROUNDING_HPP_
#define R_SRC_MODE_FP_ROUNDING_HPP_

namespace Mode::FP {
    /** FP modes supported by claripy */
    enum class Rounding {
        NearestTiesEven,
        NearestTiesAwayFromZero,
        TowardsZero,
        TowardsPositiveInf,
        TowardsNegativeInf
    };
} // namespace Mode::FP

#endif
