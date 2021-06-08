/**
 * @file
 * @brief This file defines a floating point width class
 */
#ifndef R_MODE_FP_WIDTH_HPP_
#define R_MODE_FP_WIDTH_HPP_

#include <cstdint>
#include <ostream>


namespace Mode::FP {

    /** A floating point width struct */
    struct Width {
        /** The width of the exponent */
        const uint32_t exp;
        /** The width of the mantissa */
        const uint32_t mantissa;
    };

    /** A single wide fp width */
    static inline const constexpr Width flt { 8, 24 };

    /** A double wide fp width */
    static inline const constexpr Width dbl { 11, 53 };

    /** Equality operator */
    inline bool operator==(const Width &a, const Width &b) noexcept {
        return (a.exp == b.exp) && (a.mantissa == b.mantissa);
    }

    /** Width stream operator */
    inline std::ostream &operator<<(std::ostream &os, const Width &w) {
        os << "Width(" << w.exp << ", " << w.mantissa << ")";
        return os;
    }

} // namespace Mode::FP

#endif
