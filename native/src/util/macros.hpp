/**
 * @file
 * \ingroup util
 * @brief This file defines macros used across Util
 */
#ifndef R_UTIL_MACROS_HPP_
#define R_UTIL_MACROS_HPP_


/** An abbreviation for 'const constexpr bool' to enforce consistency */
#define UTILS_CCBOOL const constexpr bool

/** An abbreviation for 'inline const constexpr bool' to enforce consistency
 *  Note that constexpr may not imply inline here so we are explicit
 */
#define UTILS_ICCBOOL const inline constexpr bool


#endif
