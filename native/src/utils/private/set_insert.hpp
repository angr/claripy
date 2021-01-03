/**
 * @file
 * \ingroup utils
 * @brief This file defines helper methods for Utils::set_join
 */
#ifndef __UTILS_PRIVATE_SETINSERT_HPP__
#define __UTILS_PRIVATE_SETINSERT_HPP__

#include <set>


namespace Utils::Private {

    /** Copy right into left */
    template <typename T> inline void set_insert(std::set<T> &left, const std::set<T> &right) {
        left.insert(right.cbegin(), right.cend());
    }

} // namespace Utils::Private

#endif
