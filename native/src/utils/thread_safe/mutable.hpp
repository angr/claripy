/**
 * @file
 * \ingroup utils
 * @brief This file defines a thread-safe mutable wrapper class
 */
#ifndef __UTILS_THREADSAFE_MUTABLE_HPP__
#define __UTILS_THREADSAFE_MUTABLE_HPP__

#include "base.hpp"
#include "move_lock.hpp"

#include "../is_same.hpp"

#include <shared_mutex>


/** Used to structure-bind to the return values of unique
 *  Var is the name of the variable the refernece will be stored in
 *  What is the ThreadSafe::Mutable to be passed to it
 */
#define UTILS_THREADSAFE_MUTABLE_UNIQUE(VAR, WHAT)                                                \
    static_assert(                                                                                \
        Utils::is_same_ignore_cv<Utils::ThreadSafe::Mutable, decltype(WHAT)>,                     \
        "UTILS_THREADSAFE_MUTABLE_UNIQUE passed non-ThreadSafe::Mutable WHAT argument");          \
    auto [VAR, _##VAR##_lock] { WHAT.unique() };

/** Used to structure-bind to the return values of shared
 *  Var is the name of the variable the refernece will be stored in
 *  What is the ThreadSafe::Mutable to be passed to it
 */
#define UTILS_THREADSAFE_MUTABLE_SHARED(VAR, WHAT)                                                \
    static_assert(                                                                                \
        Utils::is_same_ignore_cv<Utils::ThreadSafe::Mutable, decltype(WHAT)>,                     \
        "UTILS_THREADSAFE_MUTABLE_SHARED passed non-ThreadSafe::Mutable WHAT argument");          \
    const auto [VAR, _##VAR##_lock] { WHAT.shared() };


namespace Utils::ThreadSafe {

    /** Takes in a type T to hold
     *  Takes in a SharedMutex type, default to std::shared_mutex
     *  Note that you shared() and unique() behave s.t. auto A = shared() behaves
     *  the same as auto && A = shared(). This is because the first element of
     *  the pair is a reference value, and the second is not copy-constructable
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

        /** Request read-write access
         *  Structure bind to the return type as follows:
         *  auto [ref, lock] = mutable.unique();
         *  Or use the provided macro
         */
        [[nodiscard]] auto unique() {
            return std::pair<T &, const UniqueLock>{obj, &m};
        }

        /** Request read-only access
         *  Structure bind to the return type as follows:
         *  const auto [ref, lock] = mutable.shared();
         *  Or use the provided macro
         */
        [[nodiscard]] auto shared() const {
            return std::pair<const T &, const SharedLock>{obj, &m};
        }

      private:
        /** A mutex to protect the the object */
        mutable SharedMutex m {};

        /** The object being protected */
        T obj;

        // Delete other methods of construction / assignment
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(Mutable, delete);
    };

} // namespace Utils::ThreadSafe

#endif
