/**
 * @file
 * @brief This file defines a floating point width class
 */
#ifndef R_MODE_FP_WIDTH_HPP_
#define R_MODE_FP_WIDTH_HPP_

#include "../../constants.hpp"

#include <cstdint>
#include <ostream>


namespace Mode::FP {

    /** A floating point width struct */
    struct Width final {
        /** The width of the exponent */
        const uint32_t exp;
        /** The width of the mantissa, including the implicit 1 bit */
        const uint32_t mantissa;
        /** The width of the mantissa, excluding the implicit 1 bit */
        constexpr uint32_t mantissa_raw() const noexcept { return mantissa - 1; }
        /** The full width of the fp */
        constexpr Constants::UInt width() const noexcept { return 1 + no_sign_width(); }
        /** The full width of the fp */
        constexpr Constants::UInt no_sign_width() const noexcept { return exp + mantissa - 1; }
    };

    /** A single wide fp width */
    static inline const constexpr Width flt { 8, 23 + 1 };

    /** A double wide fp width */
    static inline const constexpr Width dbl { 11, 52 + 1 };

    /** Equality operator */
    constexpr bool operator==(const Width &a, const Width &b) noexcept {
        return (a.exp == b.exp) && (a.mantissa == b.mantissa);
    }

    /** Width stream operator */
    inline std::ostream &operator<<(std::ostream &os, const Width &w) {
        os << "Width(" << w.exp << ", " << w.mantissa << ")";
        return os;
    }

} // namespace Mode::FP

#endif
