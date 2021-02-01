/**
 * @file
 * \ingroup utils
 * @brief This file defines const_eval
 */
#ifndef __UTILS_CONSTEVAL_HPP__
#define __UTILS_CONSTEVAL_HPP__

namespace Utils {

    /** Force compile-time evaluation of T V
     *  Technically const_eval itself may not be evaluated at compile time
     *  But since V is guaranteed to be evaluated, any compiler should
     *  eval const_eval at compile time assuming optimizations are enabled
     */
    template <typename T, T V> const constexpr T const_eval { V };

} // namespace Utils

#endif
