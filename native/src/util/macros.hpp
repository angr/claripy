/**
 * @file
 * \ingroup util
 * @brief This file defines macros used across Util
 */
#ifndef R_SRC_UTIL_MACROS_HPP_
#define R_SRC_UTIL_MACROS_HPP_


/** An abbreviation for 'const constexpr bool' to enforce consistency */
#define UTIL_CCBOOL const constexpr bool

/** An abbreviation for 'inline const constexpr bool' to enforce consistency
 *  Note that constexpr may not imply inline here so we are explicit
 */
#define UTIL_ICCBOOL const inline constexpr bool


#endif
