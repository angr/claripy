/**
 * @file constants.hpp
 * @brief This file contains constants used across claricpp
 */
#ifndef __CONSTANTS_HPP__
#define __CONSTANTS_HPP__

#include <cstdint>

/** A signed integer type that is consistent across all of claricpp
 *  Note that python does not have an integer maximum, C++ is bounded by this restriction
 */
using Int = int_fast64_t;
/** An unsigned integer type that is consistent across all of claricpp
 *  Note that python does not have an integer maximum, C++ is bounded by this restriction
 */
using UInt = uint_fast64_t;

#endif
