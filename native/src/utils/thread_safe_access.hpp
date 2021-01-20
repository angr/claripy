/**
 * @file
 * \ingroup utils
 * @brief This file defines the ThreadSafeAccess class
 */
#ifndef __UTILS_THREADSAFEACCESS_HPP__
#define __UTILS_THREADSAFEACCESS_HPP__

#include "../macros.hpp"

#include <algorithm>
#include <memory>
#include <shared_mutex>
#include <type_traits>


namespace Utils {

    /** A class that exposes thread-safe setters and getters for a T
     *  Warning: This does not protect T internally; it only protects setting and getting
     */
    template <typename T> class ThreadSafeAccess {
      public:
        /** The get-able type */
        using Ptr = std::shared_ptr<T>;

        /** A getter */
        Ptr get() const {
            std::shared_lock<std::shared_mutex>(this->m);
            return this->obj;
        }

        /** Clear the internals */
        void clear() {
            std::unique_lock<decltype(this->m)>(this->m);
            this->obj.reset();
        }

        /************************************************/
        /*                 Constructors                 */
        /************************************************/

        /** Construct and point to nothing by default */
        ThreadSafeAccess() = default;

        /** shared_ptr constructor
         *  This is by value to allow temporary shared pointers to be used
         */
        // cppcheck-suppress nullPointer
        ThreadSafeAccess(const Ptr ptr) : m(), obj(ptr) {}

        /** Disable copy constructor */
        ThreadSafeAccess(const ThreadSafeAccess &) = delete;

        /** Disable move constructor */
        ThreadSafeAccess(ThreadSafeAccess &&) = delete;

        /************************************************/
        /*                   Setters                    */
        /************************************************/

        /** A setter that takes in a shared pointer of type type */
        void set_shared_ptr(Ptr &ptr) { this->set(ptr); }


        /** A setter by default constructor */
        template <typename U = T> void set_default() { this->set(new U); }

        /** A setter by copy constructor */
        template <typename U> void set_copy(const U &t) { this->set(new U(t)); }

        /** A setter by move constructor */
        template <typename U> void set_copy(U &&t) { this->set(new U(std::forward<U>(t))); }


        /** A setter by emplacement with args passed by copy
         *  A specialization that requires no U parameter
         */
        template <typename... Args> void set_emplace_ref_copy(Args... args) {
            this->set(new T(std::forward<Args>(args)...));
        }

        /** A setter by emplacement with args passed by copy
         *  The general definition
         */
        template <typename U, typename... Args> void set_emplace_ref_copy(Args... args) {
            this->set(new U(std::forward<Args>(args)...));
        }


        /** A setter by emplacement with args passed by const reference
         *  A specialization that requires no U parameter
         */
        template <typename... Args> void set_emplace_ref_args(const Args &...args) {
            this->set(new T(args...));
        }

        /** A setter by emplacement with args passed by const reference
         *  The general definition
         */
        template <typename U, typename... Args> void set_emplace_ref_args(const Args &...args) {
            this->set(new U(args...));
        }


        /** A setter by emplacement with args passed by forward reference
         *  A specialization that requires no U parameter
         */
        template <typename... Args> void set_emplace_foward_args(Args &&...args) {
            this->set(new T(std::forward<Args>(args)...));
        }

        /** A setter by emplacement with args passed by forward reference
         *  The general definition
         */
        template <typename U, typename... Args> void set_emplace_forward_args(Args &&...args) {
            this->set(new U(std::forward<Args>(args)...));
        }

      private:
        /** A private member used to set m safely */
        void set(Ptr ptr) {
            std::unique_lock<decltype(this->m)>(this->m);
            this->obj = ptr;
        }

        /** A private member used to set m safely */
        template <typename U> void set(U *const o) {
            static_assert(std::is_base_of_v<T, U>, "ThreadSafeAccess.set requires U subclass T");
            std::unique_lock<decltype(this->m)>(this->m);
            this->obj.reset(o);
        }

        /** A mutex to protect obj */
        mutable std::shared_mutex m;

        /** The object protected by this class */
        Ptr obj;
    };

} // namespace Utils

#endif
