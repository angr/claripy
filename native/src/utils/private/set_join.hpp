/**
 * @file
 * @brief This file defines helper methods for Utils::set_join
 */
#ifndef __UTILS_PRIVATE_SETJOIN_HPP__
#define __UTILS_PRIVATE_SETJOIN_HPP__

#include <set>


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used to designate certain items in utils as private
     *  These functions should not be called outside of the utils directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** A helper function used to merge a set of set<T>'s into ret
         *  A specialization of set_join that handles the single argument case
         */
        template <typename T> void set_join(std::set<T> &ret, const std::set<T> &a) {
            ret.insert(a.begin(), a.end());
        }

        /** A helper function used to merge a set of set<T>'s into ret
         *  Merge the set a into ret then recurse
         */
        template <typename T, typename... Args>
        void set_join(std::set<T> &ret, const std::set<T> &a, const Args... args) {
            ret.insert(a.begin(), a.end());
            set_join(ret, std::forward<const Args>(args)...);
        }

    } // namespace Private

} // namespace Utils

#endif
