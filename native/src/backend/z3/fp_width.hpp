/**
 * @file
 * @brief This file defines a floating point width class
 */
#ifndef R_BACKEND_Z3_FPWIDTH_HPP_
#define R_BACKEND_Z3_FPWIDTH_HPP_

#include "../../constants.hpp"


namespace Backend::Z3::FP {

    /** A floating point width struct */
    struct Width {
        /** The width of the exponent */
        Constants::UInt exp;
        /** The width of the mantissa */
        Constants::UInt mantissa;
    };

    /** A single wide fp width */
    static inline const constexpr Width flt { 8, 24 };

    /** A double wide fp width */
    static inline const constexpr Width dbl { 11, 53 };

    /** Equality operator */
    inline bool operator==(const Width &a, const Width &b) noexcept {
        return (a.exp == b.exp) && (a.mantissa == b.mantissa);
    }

} // namespace Backend::Z3::FP

#endif
