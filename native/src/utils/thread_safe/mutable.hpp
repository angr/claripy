/**
 * @file
 * \ingroup utils
 * @brief This file defines a thread-safe mutable wrapper class
 */
#ifndef R_UTILS_THREADSAFE_MUTABLE_HPP_
#define R_UTILS_THREADSAFE_MUTABLE_HPP_

#include "base.hpp"
#include "move_lock.hpp"
#include "protected_object.hpp"

#include "../is_same.hpp"

#include <shared_mutex>


namespace Utils::ThreadSafe {

    /** Takes in a type T to hold
     *  Takes in a SharedMutex type, default to std::shared_mutex
     *  Note that you shared() and unique() behave s.t. auto A = shared() behaves
     *  the same as auto && A = shared(). This is because the first element of
     *  the pair is a reference value, and the second is not copy-constructable
     *  Warning: Do not copy the reference outside of the scope where the lock exists
     */
    template <typename T, typename SharedMutex = std::shared_mutex>
    class Mutable final : public Base {
        /** The moveable lock type returned */
        template <bool Shared> using MLock = MoveLock<SharedMutex, Shared>;

        /** Unique Lock */
        using UniqueLock = MLock<false>;
        /** Shared Lock */
        using SharedLock = MLock<true>;

      public:
        /** Default constructor, default constructs T */
        Mutable() = default;

        /** Emplacement constructor, take object by move */
        Mutable(T &&o) : Base { std::forward<Base>(o) }, obj { o } {}

        /** Destructor */
        ~Mutable() noexcept override final = default;

        /** Request read-write access
         */
        [[nodiscard]] auto unique() { return ProtectedObject { obj, UniqueLock { m } }; }

        /** Request scoped read-write access
         *  Structure bind to the return type as follows:
         *  auto [ref, lock] = mutable.unique();
         */
        [[nodiscard]] auto scoped_unique() { return std::pair<T &, const UniqueLock> { obj, m }; }

        /** Request read-only access
         */
        [[nodiscard]] auto shared() { return ProtectedObject { obj, SharedLock { m } }; }

        /** Request scoped read-only access
         *  Structure bind to the return type as follows:
         *  const auto [ref, lock] = mutable.shared();
         */
        [[nodiscard]] auto scoped_shared() const {
            return std::pair<const T &, const SharedLock> { obj, m };
        }

      private:
        /** A mutex to protect the the object */
        mutable SharedMutex m {};

        /** The object being protected */
        T obj;

        // Delete other methods of construction / assignment
        SET_IMPLICITS_OPERATORS(Mutable, delete);
        /** Delete copy constructor */
        Mutable(const Mutable &) = delete;
    };

} // namespace Utils::ThreadSafe

#endif
