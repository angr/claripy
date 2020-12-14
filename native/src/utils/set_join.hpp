/**
 * @file set_join.hpp
 * @brief This file defines a method to join a set of set<T>'s together
 */
#ifndef __UTILS_SET_JOIN_HPP__
#define __UTILS_SET_JOIN_HPP__

#include <set>


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used to designate certain items in utils as private
     *  These functions should not be called outside of the utils directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {
        /** A helper function used to merge a set of set<T>'s into ret
         *  A specialization of set_join_helper that handles the single argument case
         */
        template <typename T> void set_join_helper(std::set<T> &ret, const std::set<T> &a) {
            ret.insert(a.begin(), a.end());
        }

        /** A helper function used to merge a set of set<T>'s into ret
         *  Merge the set a into ret then recurse
         */
        template <typename T, typename... Args>
        void set_join_helper(std::set<T> &ret, const std::set<T> &a, const Args... args) {
            ret.insert(a.begin(), a.end());
            set_join_helper(ret, std::forward<const Args>(args)...);
        }
    } // namespace Private

    /** Joins a set of set<T>'s into one
     *  Requires at least two arguments.
     *  Can automatically deduce template types from arguments
     */
    template <typename T, typename... Args>
    std::set<T> set_join(const std::set<T> &s1, const Args... args) {
        auto ret = std::set<T>();
        Private::set_join_helper<T>(ret, std::forward<decltype(s1)>(s1),
                                    std::forward<const Args>(args)...);
        return ret;
    }

} // namespace Utils

#endif
