/**
 * @file
 * \ingroup util
 * @brief This file defines ProtectedObject
 */
#ifndef R_UTIL_THREADSAFE_PROTECTEDOBJECT_HPP_
#define R_UTIL_THREADSAFE_PROTECTEDOBJECT_HPP_

#include "base.hpp"
#include "move_lock.hpp"

#include "../assert.hpp"
#include "../err.hpp"
#include "../fallback_error_log.hpp"
#include "../macros.hpp"
#include "../terminate.hpp"

#include <shared_mutex>


namespace Util::ThreadSafe {

    /** Contains a pointer to an object and a locked lock protecting it
     *  Note: Lock should *not* be a mutex, but rather a lock that guards a mutex
     */
    template <typename T, typename Lock> class ProtectedObject final : Base {
      private:
        /** A pointer to the object being protected */
        T *pointer;
        /** Lock */
        mutable Lock lock;

      public:
        // Constructors / destructors

        /** Constructor
         *  Warning: This assumes l is already locked
         */
        explicit ProtectedObject(T &r, Lock &&l) noexcept : pointer { &r }, lock { std::move(l) } {}

        /** Move Constructor */
        ProtectedObject(ProtectedObject &&o) noexcept
            : Base { std::forward<Base>(o) }, pointer { o.pointer }, lock { std::move(o.lock) } {
            o.pointer = nullptr;
        }

        /** Move Assignment */
        ProtectedObject &operator=(ProtectedObject &&o) noexcept {
            if (this != &o) {
                Base::operator=(std::forward<Base>(o));
                lock = std::move(o.lock);
                pointer = o.pointer;
                o.pointer = nullptr;
            }
            return *this;
        }

        /** Default destructor */
        ~ProtectedObject() noexcept final = default;

        // Getters

        /** Return true if the stored reference is const */
        inline bool ref_is_const() const noexcept { return std::is_const_v<T>; }

/** A local macro that will enable a function if T is not const */
#define ENABLE_IF_T_MUTABLE(RET)                                                                   \
    template <typename U = T> std::enable_if_t<sizeof(U) && !std::is_const_v<T>, RET>

/** A local macro that will enable a function if T is not const */
#define ENABLE_OP_IF_T_MUTABLE(TYPE)                                                               \
    template <typename U = T>                                                                      \
    ProtectedObject &operator=(std::enable_if_t<sizeof(U) && !std::is_const_v<T>, TYPE> o)

        /** Get the internal pointer; generally the -> operator should be preferred
         *  Warning: Do *not* let this pointer dangle
         */
        const T *unprotected_ptr() const { return ptr(); }

        /** Get the internal reference */
        ENABLE_IF_T_MUTABLE(T *) unprotected_ptr() { return ptr(); }

        /** Get the internal reference; generally the -> operator should be preferred
         *  Warning: Do *not* let this reference dangle
         */
        const T &unprotected_ref() const { return ref(); }

        /** Get the internal reference */
        ENABLE_IF_T_MUTABLE(T &) unprotected_ref() { return ref(); }

        // Operators

        /** Copy assignment */
        ENABLE_OP_IF_T_MUTABLE(const T &) {
            nullcheck(false);
            ref() = o;
            return *this;
        }

        /** We expose this operator to be the '.' operator, it is protected by the lock */
        T *operator->() noexcept { return ptr(); }

        /** We expose this operator to be the '.' operator, it is protected by the lock */
        ENABLE_IF_T_MUTABLE(const T *) operator->() const noexcept {
            nullcheck(true);
            return ptr;
        }

      private:
        /** Warns if ptr is nullptr; terminates the program if critical */
        inline void nullcheck(const bool critical) const noexcept {
            if (UNLIKELY(pointer == nullptr)) {
                static const constexpr auto term { [](CCSC m) { Util::terminate(m, false); } };
                (critical ? term : fallback_error_log)(
                    "ProtectedObject trying to operate on a nullptr; this probably indicates "
                    "improper usage of a ThreadSafe object.");
            }
        }

        /** Return a T pointer */
        const T *ptr() const noexcept { return pointer; }
        /** Return a T pointer */
        ENABLE_IF_T_MUTABLE(T *) ptr() noexcept { return pointer; }

        /** Return a T reference */
        const T &ref() const noexcept {
            nullcheck(true);
            return *pointer;
        }
        ENABLE_IF_T_MUTABLE(T &) ref() noexcept {
            nullcheck(true);
            return *pointer;
        }

        /** Delete copy constructor */
        ProtectedObject(const ProtectedObject &) = delete;

        /** Delete copy assignment operator */
        ProtectedObject &operator=(const ProtectedObject &) = delete;

// Cleanup
#undef ENABLE_IF_T_MUTABLE
#undef ENABLE_OP_IF_T_MUTABLE
    };


} // namespace Util::ThreadSafe

#endif
