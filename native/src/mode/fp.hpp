/**
 * @file
 * @brief This file defines FP modes
 */
#ifndef R_MODE_FP_HPP_
#define R_MODE_FP_HPP_


namespace Mode {

    /** FP modes supported by claripy */
    enum class FP {
        NearestTiesEven = 0,
        NearestTiesAwayFromZero,
        TowardsZero,
        TowardsPositiveInf,
        TowardsNegativeInf
    };

} // namespace Mode

#endif
