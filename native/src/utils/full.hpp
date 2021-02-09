/**
 * @file
 * \ingroup utils
 * @brief This file defines a best effort thread-safe guess of if a shared_ptr is full / empty.
 * Note: Our guesses rely on likely undocumented behavior of shared_ptr; they *should* never fail
 */
#ifndef __UTILS_FULL_HPP__
#define __UTILS_FULL_HPP__

#include <memory>


namespace Utils {

    /** A best guess that returns true if we think the pointer is not empty
     *  Note: This relies on likely undocumented behavior of shared_ptr; it *should* never fail
     *  Return true if p is empty
     *  Note: if p is empty, the object p points to, if not nullptr, may not be done destructing
     */
    template <typename T> inline bool empty(const std::shared_ptr<T> &p) {
        return p.use_count() == 0;
    }

    /** A best guess that returns true if we think the pointer is not empty
     *  Note: This relies on likely undocumented behavior of shared_ptr; it *should* never fail
     *  Return true if p is not empty
     *  Note: if p is empty, the object p points to, if not nullptr, may not be done destructing
     */
    template <typename T> inline bool full(const std::shared_ptr<T> &p) { return !empty(p); }

} // namespace Utils

#endif
