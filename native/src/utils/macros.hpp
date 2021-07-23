/**
 * @file
 * \ingroup utils
 * @brief This file defines macros used across Utils
 */
#ifndef R_UTILS_MACROS_HPP_
#define R_UTILS_MACROS_HPP_


/** An abbreviation for 'const constexpr bool' to enforce consistency */
#define UTILS_CCBOOL const constexpr bool

/** An abbreviation for 'inline const constexpr bool' to enforce consistency
 *  Note that constexpr may not imply inline here so we are explicit
 */
#define UTILS_ICCBOOL const inline constexpr bool


#endif
