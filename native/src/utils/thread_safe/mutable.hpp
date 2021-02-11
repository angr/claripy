/**
 * @file
 * \ingroup utils
 * @brief This file defines a thread-safe mutable wrapper class
 */
#ifndef __UTILS_THREADSAFE_MUTABLE_HPP__
#define __UTILS_THREADSAFE_MUTABLE_HPP__

#include "move_lock.hpp"

#include <shared_mutex>


namespace Utils::ThreadSafe {

    /** Takes in a type T to hold
     *  Takes in a SharedMutex type, default to std::shared_mutex
     */
    template <typename T, typename SharedMutex = std::shared_mutex> class Mutable final {
        /** The moveable lock type returned */
        template <bool Shared> using MLock = MoveLock<SharedMutex, Shared>;

      public:
        /** Emplacement constructor, take object by move */
        Mutable(T &&o) : obj { o } {}

        /** Request read-write access */
        [[nodiscard]] auto unique() {
            return std::pair<T &, const MLock<false>>(obj, MLock<false> { &m });
        }

        /** Request read-only access */
        [[nodiscard]] auto shared() const {
            return std::pair<const T &, const MLock<true>>(obj, MLock<true> { &m });
        }

      private:
        /** A mutex to protect the the object */
        mutable SharedMutex m;

        /** The object being protected */
        T obj;

        // Delete other methods of construction / assignment
        SET_IMPLICITS(Mutable, delete)
    };

} // namespace Utils::ThreadSafe

#endif
