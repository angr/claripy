/**
 * @file
 * @brief This file contains constants used across claricpp
 */
#ifndef __CONSTANTS_HPP__
#define __CONSTANTS_HPP__

#include <cstdint>
#include <limits>
#include <stdexcept>
#include <type_traits>


namespace Constants {

    /** A signed integer type that is consistent across all of claricpp
     *  Note that python does not have an integer maximum, C++ is bounded by this restriction
     *  Guaranteed to be a primitive (noexcept construction, for example, can be assumed)
     */
    using Int = int_fast64_t;

    /** An unsigned integer type that is consistent across all of claricpp
     *  Note that python does not have an integer maximum, C++ is bounded by this restriction
     *  Guaranteed to be a primitive (noexcept construction, for example, can be assumed)
     */
    using UInt = uint_fast64_t;

    /** An abreviation for const char * */
    using CCS = const char *;

    /** An abreviation for const char * const */
    using CCSC = CCS const;

} // namespace Constants


/** Verify Constants::Int is a primitive */
static_assert(std::is_arithmetic_v<Constants::Int>,
              "Constants::Int must be an arithmetic primitive");
/** Verify Constants::UInt is a primitive */
static_assert(std::is_arithmetic_v<Constants::UInt>,
              "Constants::UInt must be an arithmetic primitive");


/** Create a literal prefix for Constants::Int
 *  This assumes the max of
 */
constexpr inline Constants::Int operator"" _i(const unsigned long long i) {
    // If it is safe, cast
    const constexpr auto max { std::numeric_limits<Constants::Int>::max() };
    const constexpr auto lim { static_cast<unsigned long long>(max) };
    if ((i <= lim) && (static_cast<Constants::Int>(i) <= max)) {
        return static_cast<Constants::Int>(i);
    }
    // Otherwise we would have to narrow
    else {
        // Narrowing
        throw std::domain_error("Constant given to literal operator too large");
    }
}


/** Create a literal prefix for Constants::UInt */
constexpr inline Constants::UInt operator"" _ui(const unsigned long long u) noexcept {
    return u; // The compiler will error if this is narrowing
}

/** A way to get a char * from a char[]
 *  char[]'s may not be forwardable, _c alleviates this
 */
constexpr inline Constants::CCS operator"" _c(Constants::CCS s, unsigned long) noexcept {
    return s;
}

#endif
