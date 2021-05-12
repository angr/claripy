/**
 * @file
 * \ingroup utils
 * @brief This file ProtectedObject
 */
#ifndef __UTILS_THREADSAFE_PROTECTEDOBJECT_HPP__
#define __UTILS_THREADSAFE_PROTECTEDOBJECT_HPP__

#include "base.hpp"
#include "move_lock.hpp"

#include "../affirm.hpp"
#include "../error.hpp"
#include "../is_same.hpp"
#include "../macros.hpp"

#include <shared_mutex>
#include <type_traits>


namespace Utils::ThreadSafe {

    /** Contains a pointer to an object and a locked lock protecting it
     *  Note: Lock should *not* be a mutex, but rather a lock that guards a mutex
     */
    template <typename T, typename Lock> class ProtectedObject final : Base {
      public:
        /** Constructor */
        ProtectedObject(T &r, Lock &&l) noexcept : pointer { &r }, lock { std::move(l) } {}

        /** Move Constructor */
        ProtectedObject(ProtectedObject &&o) noexcept
            : pointer { o.pointer }, lock { std::move(o.lock) } {
            o.pointer = nullptr;
        }

        /** Move Assignment */
        ProtectedObject &operator=(ProtectedObject &&o) noexcept {
            if (this != &o) {
                pointer = o.pointer;
                o.pointer = nullptr;
                lock = std::move(o.lock);
            }
            return *this;
        }

        /** Default destructor */
        ~ProtectedObject();

        // Getters

        /** Return true if the stored reference is const */
        inline bool ref_is_const() const noexcept { return std::is_const_v<T>; }

/** A local macro that will enable a function if T is not const */
#define ENABLE_IF_T_MUTABLE(RET)                                                                  \
    template <typename U = T> std::enable_if_t<sizeof(U) && !std::is_const_v<T>, RET>

/** A local macro that will enable a function if T is not const */
#define ENABLE_OP_IF_T_MUTABLE(TYPE)                                                              \
    template <typename U = T>                                                                     \
    ProtectedObject &operator=(std::enable_if_t<sizeof(U) && !std::is_const_v<T>, TYPE> o)

        /** Get the internal pointer; generally the -> operator should be preferred
         *  Warning: Do *not* let this pointer dangle
         */
        const T &unprotected_ptr() const { return ptr(); }

        /** Get the internal reference */
        ENABLE_IF_T_MUTABLE(T &) unprotected_ptr() { return ptr(); }

        /** Get the internal reference; generally the -> operator should be preferred
         *  Warning: Do *not* let this reference dangle
         */
        const T &unprotected_ref() const { return ref(); }

        /** Get the internal reference */
        ENABLE_IF_T_MUTABLE(T &) unprotected_ref() { return ref(); }

        // Operators

        /** Copy assignment */
        ENABLE_OP_IF_T_MUTABLE(const T &) {
            throw_if_null();
            ref() = o;
            return *this;
        }

        /** We expose this operator to be the '.' operator, except that it is still
         *  protected by the lock
         */
        T *operator->() noexcept { return ptr(); }

        /** We expose this operator to be the '.' operator, except that it is still
         *  protected by the lock
         */
        ENABLE_IF_T_MUTABLE(const T *) operator->() const noexcept {
            throw_if_null();
            return ptr;
        }

      private:
        /** Throws an exception if ptr is nullptr */
        template <typename Err = Utils::Error::Unexpected::IncorrectUsage>
        void throw_if_null() const {
            Utils::affirm<Err>(pointer,
                               WHOAMI_WITH_SOURCE "attempted to dereference a null pointer");
        }

        /** Return a T pointer */
        const T *ptr() const {
            throw_if_null();
            return pointer;
        }
        /** Return a T pointer */
        ENABLE_IF_T_MUTABLE(T *) ptr() {
            throw_if_null();
            return pointer;
        }

        /** Return a T reference */
        const T &ref() const {
            throw_if_null();
            return *pointer;
        }
        ENABLE_IF_T_MUTABLE(T &) ref() {
            throw_if_null();
            return *pointer;
        }

        /** Delete copy constructor */
        ProtectedObject(const ProtectedObject &) = delete;
        /** Delete copy assignment operator */
        ProtectedObject &operator=(const ProtectedObject &) = delete;

        /** A pointer to the object being protected */
        T *pointer;
        /** Lock */
        mutable Lock lock;

// Cleanup
#undef ENABLE_IF_T_MUTABLE
#undef ENABLE_OP_IF_T_MUTABLE
    };


} // namespace Utils::ThreadSafe

#endif
