/**
 * @file
 * @brief This file contains constants used across claricpp
 */
#ifndef __CONSTANTS_HPP__
#define __CONSTANTS_HPP__

#include <cstdint>


namespace Constants {

    /** A signed integer type that is consistent across all of claricpp
     *  Note that python does not have an integer maximum, C++ is bounded by this restriction
     */
    using Int = int_fast64_t;

    /** An unsigned integer type that is consistent across all of claricpp
     *  Note that python does not have an integer maximum, C++ is bounded by this restriction
     */
    using UInt = uint_fast64_t;

    /** An abreviation for const char * */
    using CCS = const char *;

    /** An abreviation for const char * const */
    using CCSC = CCS const;

} // namespace Constants


/** Create a literal prefix for Constants::Int */
constexpr Constants::Int operator"" _i(const unsigned long long i) {
    return Constants::Int(i);
}


/** Create a literal prefix for Constants::UInt */
constexpr Constants::UInt operator"" _ui(const unsigned long long u) {
    return Constants::UInt(u);
}


#endif
