/**
 * @file
 * \ingroup utils
 * @brief This file defines the ThreadSafeAccess class
 */
#ifndef __UTILS_THREADSAFEACCESS_HPP__
#define __UTILS_THREADSAFEACCESS_HPP__

#include "make_derived_shared.hpp"

#include "../macros.hpp"

#include <algorithm>
#include <memory>
#include <mutex>
#include <shared_mutex>
#include <type_traits>


namespace Utils {

    /** A class that exposes thread-safe setters and getters for a T
     *  Warning: This does not protect T internally; it only protects setting and getting
     */
    template <typename Base> class ThreadSafeAccess final {
      public:
        /** The get-able type */
        using Ptr = std::shared_ptr<const Base>;

        /** A getter */
        Ptr get() const {
            std::shared_lock<std::shared_mutex>(this->m);
            return this->obj;
        }

        /** Clear the internals */
        void clear() {
            std::lock_guard<decltype(this->m)>(this->m);
            this->obj.reset();
        }

        /************************************************/
        /*                 Constructors                 */
        /************************************************/

        /** Construct and point to nothing by default */
        ThreadSafeAccess() = default;

        /** Ptr constructor
         *  This is by value to allow temporary shared pointers to be used
         */
        // cppcheck-suppress nullPointer
        explicit ThreadSafeAccess(const Ptr ptr) : obj(ptr) {}

        /** Copy constructor */
        ThreadSafeAccess(const ThreadSafeAccess &old) : obj(old.get()) {}

        /** Move constructor is just a copy
         *  Because of our lock, we cannot specify noexcept
         */
        ThreadSafeAccess(ThreadSafeAccess &&old) : obj(old.get()) {} // NOLINT

        /** Copy assignment */
        ThreadSafeAccess &operator=(const ThreadSafeAccess &old) {
            this->set_ref(old.get());
            return *this;
        }

        /** Move assignment is copy assignment
         *  Because of our lock, we cannot specify noexcept
         */
        ThreadSafeAccess &operator=(ThreadSafeAccess &&old) { return (*this = old); } // NOLINT

        /************************************************/
        /*                   Setters                    */
        /************************************************/

        /** A setter that takes in a shared pointer of type type */
        void set_shared_ptr(const Ptr &ptr) { this->set_ref(ptr); }

        /** A setter that takes in a shared pointer of type type */
        void set_shared_ptr_move(Ptr &&ptr) { this->set_move(std::forward<Ptr>(ptr)); }


        /** A setter by default constructor */
        template <typename Derived = Base> void set_default() {
            this->set_move(std::move(make_derived_shared<Base, Derived>()));
        }

        /** A setter by copy constructor */
        template <typename Derived = Base> void set_copy(const Derived &t) {
            this->set_move(std::move(make_derived_shared<Base, Derived>(t)));
        }

        /** A setter by move constructor */
        template <typename Derived = Base> void set_move(Derived &&t) {
            this->set_move(
                std::move(make_derived_shared<Base, Derived>(std::forward<Derived>(t))));
        }


        /** A setter by emplacement with args passed by copy
         *  A specialization that requires no Derived parameter
         */
        template <typename... Args> void set_emplace_ref_copy(Args... args) {
            this->set_emplace_forward_args(std::forward<Args>(args)...);
        }

        /** A setter by emplacement with args passed by copy
         *  The general definition
         */
        template <typename Derived, typename... Args> void set_emplace_ref_copy(Args... args) {
            this->set_emplace_forward_args<Derived>(std::forward<Args>(args)...);
        }


        /** A setter by emplacement with args passed by const reference
         *  A specialization that requires no Derived parameter
         */
        template <typename... Args> void set_emplace_ref_args(const Args &...args) {
            this->set_move(std::move(std::make_shared<Base>(args...)));
        }

        /** A setter by emplacement with args passed by const reference
         *  The general definition
         */
        template <typename Derived, typename... Args>
        void set_emplace_ref_args(const Args &...args) {
            this->set_move(std::move(make_derived_shared<Base, Derived>(args...)));
        }


        /** A setter by emplacement with args passed by forward reference
         *  A specialization that requires no Derived parameter
         */
        template <typename... Args> void set_emplace_foward_args(Args &&...args) {
            this->set_move(std::move(std::make_shared<Base>(std::forward<Args>(args)...)));
        }

        /** A setter by emplacement with args passed by forward reference
         *  The general definition
         */
        template <typename Derived, typename... Args>
        void set_emplace_forward_args(Args &&...args) {
            this->set_move(
                std::move(make_derived_shared<Base, Derived>(std::forward<Args>(args)...)));
        }

      private:
        /** A private member used to set m safely */
        inline void set_ref(const Ptr &ptr) {
            std::lock_guard<decltype(this->m)>(this->m);
            this->obj = ptr;
        }

        /** A private member used to set m safely */
        inline void set_move(Ptr &&ptr) {
            std::lock_guard<decltype(this->m)>(this->m);
            this->obj = ptr;
        }

        /** A mutex to protect obj */
        mutable std::shared_mutex m;

        /** The object protected by this class */
        Ptr obj { nullptr };
    };

} // namespace Utils

#endif
