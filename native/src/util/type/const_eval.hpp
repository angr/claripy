/**
 * @file
 * \ingroup util
 * @brief This file defines const_eval
 */
#ifndef R_SRC_UTIL_TYPE_CONSTEVAL_HPP_
#define R_SRC_UTIL_TYPE_CONSTEVAL_HPP_

namespace Util::Type {

    /** Force compile-time evaluation of T V
     *  Technically const_eval itself may not be evaluated at compile time
     *  But since V is guaranteed to be evaluated, any compiler should
     *  eval const_eval at compile time assuming optimizations are enabled
     */
    template <typename T, T V> inline const constexpr T const_eval { V };

} // namespace Util::Type

#endif
