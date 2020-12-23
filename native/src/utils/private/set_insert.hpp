/**
 * @file
 * @brief This file defines helper methods for Utils::set_join
 */
#ifndef __UTILS_PRIVATE_SETINSERT_HPP__
#define __UTILS_PRIVATE_SETINSERT_HPP__

#include <set>


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used to designate certain items in utils as private
     *  These functions should not be called outside of the utils directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** Copy right into left */
        template <typename T> void set_insert(std::set<T> &left, const std::set<T> &right) {
            left.insert(right.cbegin(), right.cend());
        }

    } // namespace Private

} // namespace Utils

#endif
