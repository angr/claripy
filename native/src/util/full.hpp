/**
 * @file
 * \ingroup util
 * @brief This file defines a best effort thread-safe guess of if a shared_ptr is full / empty.
 * Note: If you do not need to be involved with the lifetime of the object, consider raw pointers
 * Note: Our guesses rely on likely undocumented behavior of shared_ptr; they *should* never fail
 */
#ifndef R_SRC_UTIL_FULL_HPP_
#define R_SRC_UTIL_FULL_HPP_

#include <memory>


namespace Util {

    /** A best guess that returns true if we think the pointer is not empty
     *  If you do not need to be involved with the lifetime of the object, consider raw pointers
     *  Note: This relies on likely undocumented behavior of shared_ptr; it *should* never fail
     *  Return true if p is empty
     *  Note: if p is empty, the object p points to, if not nullptr, may not be done destructing
     */
    template <typename T> inline bool empty(const std::shared_ptr<T> &p) noexcept {
        return p.use_count() == 0;
    }

    /** A best guess that returns true if we think the pointer is not empty
     *  If you do not need to be involved with the lifetime of the object, consider raw pointers
     *  Note: This relies on likely undocumented behavior of shared_ptr; it *should* never fail
     *  Return true if p is not empty
     *  Note: if p is empty, the object p points to, if not nullptr, may not be done destructing
     */
    template <typename T> inline bool full(const std::shared_ptr<T> &p) noexcept {
        return !empty(p);
    }

} // namespace Util

#endif
