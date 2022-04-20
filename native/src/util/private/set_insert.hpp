/**
 * @file
 * \ingroup util
 * @brief This file defines helper methods for Util::set_join
 */
#ifndef R_SRC_UTIL_PRIVATE_SETINSERT_HPP_
#define R_SRC_UTIL_PRIVATE_SETINSERT_HPP_

#include <set>


namespace Util::Private {

    /** Copy right into left */
    template <typename T> inline void set_insert(std::set<T> &left, const std::set<T> &right) {
        left.insert(right.cbegin(), right.cend());
    }

} // namespace Util::Private

#endif
