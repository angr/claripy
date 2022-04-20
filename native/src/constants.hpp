/**
 * @file
 * @brief This file contains constants used across claricpp
 */
#ifndef R_SRC_CONSTANTS_HPP_
#define R_SRC_CONSTANTS_HPP_

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
 *  We prefer 'long long' over int64_t if same size (makes cross platform API easier)
 */
using I64 = long long;
static_assert(sizeof(I64) == 8, "Refusing to compile; wrong size");

/** An unsigned integer type that is consistent across all of claricpp
 *  Note that python does not have an integer maximum, C++ is bounded by this restriction
 *  Guaranteed to be a primitive (noexcept construction, for example, can be assumed)
 *  We prefer 'unsigned long long' over uint64_t if same size (makes cross platform API easier)
 */
using U64 = unsigned long long;
static_assert(sizeof(U64) == 8, "Refusing to compile; wrong size");

/** A shortcut for a const Type * const */
template <typename T> using CTSC = const T *const;

/** An abbreviation for const char * const */
using CCSC = CTSC<char>;

/** Verify I64 is a primitive */
static_assert(std::is_arithmetic_v<I64>, "I64 must be an arithmetic primitive");
/** Verify U64 is a primitive */
static_assert(std::is_arithmetic_v<U64>, "U64 must be an arithmetic primitive");


/** Create a literal prefix for I64
 *  This assumes the max of
 */
constexpr I64 operator"" _i(const unsigned long long i) {
    static_assert(sizeof(I64) == sizeof(unsigned long long), "Will not narrow");
    return static_cast<I64>(i);
}

/** Create a literal prefix for U64 */
constexpr U64 operator"" _ui(const unsigned long long u) noexcept {
    static_assert(sizeof(U64) == sizeof(unsigned long long), "Will not narrow");
    return u;
}

// A way to get an std::string from a char[]
using ::std::string_literals::operator""s;

#endif
