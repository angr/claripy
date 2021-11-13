/**
 * @file
 * @brief This file contains constants used across claricpp
 */
#ifndef R_CONSTANTS_HPP_
#define R_CONSTANTS_HPP_

#include <cstdint>
#include <limits>
#include <memory>
#include <stdexcept>
#include <string>
#include <type_traits>


// Verify RTTI is enabled
#if defined(__clang__)
    #if !__has_feature(cxx_rtti)
        #error "Claricpp requires on RTTI"
    #endif
#elif defined(__GNUG__)
    #if !defined(__GXX_RTTI)
        #error "Claricpp requires on RTTI"
    #endif
#elif defined(_MSC_VER)
    #if !defined(_CPPRTTI)
        #error "Claricpp requires on RTTI"
    #endif
#elif !defined(RTTI_OVERRIDE)
    #error "Compiler unknown. If your compiler supports RTTI define RTTI_OVERRIDE"
#endif

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

/** A shortcut for a const Type * const */
template <typename T> using CTSC = const T *const;

/** An abbreviation for const char * const */
using CCSC = CTSC<char>;

/** Verify Int is a primitive */
static_assert(std::is_arithmetic_v<Int>, "Int must be an arithmetic primitive");
/** Verify UInt is a primitive */
static_assert(std::is_arithmetic_v<UInt>, "UInt must be an arithmetic primitive");


/** Create a literal prefix for Int
 *  This assumes the max of
 */
constexpr Int operator"" _i(const unsigned long long i) {
    // If it is safe, cast
    const constexpr auto max { std::numeric_limits<Int>::max() };
    const constexpr auto lim { static_cast<unsigned long long>(max) };
    if ((i <= lim) && (static_cast<Int>(i) <= max)) {
        return static_cast<Int>(i);
    }
    // Otherwise we would have to narrow
    else {
        // Narrowing
        throw std::domain_error("Constant given to literal operator: too large");
    }
}


/** Create a literal prefix for UInt */
constexpr UInt operator"" _ui(const unsigned long long u) noexcept {
    return u; // The compiler will error if this is narrowing
}

/** A way to get a char * from a char[]
 *  char[]'s may not be forwardable, _c alleviates this
 */
constexpr const char *operator"" _c(const char *s, unsigned long) noexcept {
    return s;
}

// A way to get an std::string from a char[]
using ::std::string_literals::operator""s;

#endif
