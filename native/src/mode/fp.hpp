/**
 * @file
 * @brief This file defines FP modes
 */
#ifndef __MODE_FP_HPP__
#define __MODE_FP_HPP__


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
