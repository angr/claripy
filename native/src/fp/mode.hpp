/**
 * @file
 * @brief This file defines FP modes
 */
#ifndef __FP_MODE_HPP__
#define __FP_MODE_HPP__


namespace FP {

    /** FP modes supported by claripy */
    enum class Mode {
        RM_NearestTiesEven = 0,
        RM_NearestTiesAwayFromZero,
        RM_TowardsZero,
        RM_TowardsPositiveInf,
        RM_TowardsNegativeInf
    };

} // namespace FP

#endif
