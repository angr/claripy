/**
 * @file
 * \ingroup util
 * @brief This file defines Util::ref
 */
#ifndef R_SRC_UTIL_REF_HPP_
#define R_SRC_UTIL_REF_HPP_

namespace Util {

    /** This allows passing compile-time literals by reference
     *  Note that constexpr may not imply inline here so we are explicit
     */
    template <typename T, T N> inline constexpr const T ref { N };

} // namespace Util

#endif
