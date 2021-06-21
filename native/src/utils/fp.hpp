/**
 * @file
 * \ingroup utils
 * @brief This file defines the fp function
 */
#ifndef R_UTILS_FP_HPP_
#define R_UTILS_FP_HPP_

#include "is_in.hpp"
#include "to_underlying.hpp"

#include "../constants.hpp"

#include <cmath>


namespace Utils {

    /** Create an floating point value of type T of from a mantissa, exponent and sign
     *  Note: ldexp casts items to doubles, so there might be some floating point error.
     */
    template <typename T>
    T fp(const bool positive, const Constants::UInt mantissa, const int exp) noexcept {
        static_assert(Utils::qualified_is_in<T, float, double>, "Unsupported type");
        return static_cast<T>(std::copysign(std::ldexp(mantissa, exp), (positive ? 1. : -1.)));
    }

} // namespace Utils

#endif
