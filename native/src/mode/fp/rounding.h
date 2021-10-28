/**
 * @file
 * @brief This file defines a macro which defines FP Rounding modes
 * This exists so it can be used by the C API
 */
#ifndef R_MODE_FP_ROUNDING_H_
#define R_MODE_FP_ROUNDING_H_

/** A macro defining the internals of Rounding; this is needed for the C API */
#define MODE_FP_ROUNDING_VALS(PREFIX) \
    PREFIX##NearestTiesEven = 0, \
    PREFIX##NearestTiesAwayFromZero, \
    PREFIX##TowardsZero, \
    PREFIX##TowardsPositiveInf, \
    PREFIX##TowardsNegativeInf

#endif
