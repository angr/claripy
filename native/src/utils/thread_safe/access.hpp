/**
 * @file
 * \ingroup utils
 * @brief This file defines the thread-safe Access class
 * Note: this class is similiar to std::atomic, except that unlike atomic,
 * we do note require the following to be true:
 * 1. std::is_trivially_copyable<T>::value
 * 2. std::is_copy_constructible<T>::value
 * 3. std::is_move_constructible<T>::value
 * 4. std::is_copy_assignable<T>::value
 * 5. std::is_move_assignable<T>::value
 */
#ifndef __UTILS_THREADSAFE_ACCESS_HPP__
#define __UTILS_THREADSAFE_ACCESS_HPP__

#include "base.hpp"

#include "../../macros.hpp"
#include "../make_derived_shared.hpp"

#include <algorithm>
#include <memory>
#include <mutex>
#include <shared_mutex>
#include <type_traits>


namespace Utils::ThreadSafe {

    /** A class that exposes thread-safe setters and getters for a T
     *  Warning: This does not protect T internally; it only protects setting and getting
     * Note: this class is similiar to std::atomic, except that unlike atomic,
     * we do note require the following to be true:
     * 1. std::is_trivially_copyable<T>::value
     * 2. std::is_copy_constructible<T>::value
     * 3. std::is_move_constructible<T>::value
     * 4. std::is_copy_assignable<T>::value
     * 5. std::is_move_assignable<T>::value
     */
    template <typename BaseT> class Access final : ThreadSafe::Base {
      public:
        /** The get-able type */
        using Ptr = std::shared_ptr<const BaseT>;

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
        Access() = default;

        /** Ptr constructor
         *  This is by value to allow temporary shared pointers to be used
         */
        // cppcheck-suppress nullPointer
        explicit Access(const Ptr ptr) : obj { ptr } {}

        /** Copy constructor */
        Access(const Access &old) : Base { old }, obj { old.get() } {}

        /** Move constructor is just a copy
         *  Because of our lock, we cannot specify noexcept
         */
        Access(Access &&old) : Base { std::forward<Base>(old) }, obj { old.get() } {} // NOLINT

        /** Copy assignment */
        Access &operator=(const Access &old) {
            Base::operator=(static_cast<Base>(old));
            this->set_ref(old.get());
            return *this;
        }

        /** Move assignment is copy assignment
         *  Because of our lock, we cannot specify noexcept
         */
        Access &operator=(Access &&old) {
            Base::operator=(std::forward<Base>(old));
            return (*this = old);
        }

        /************************************************/
        /*                   Setters                    */
        /************************************************/

        /** A setter that takes in a shared pointer of type type */
        void set_shared_ptr(const Ptr &ptr) { this->set_ref(ptr); }

        /** A setter that takes in a shared pointer of type type */
        void set_shared_ptr_move(Ptr &&ptr) { this->set_move(std::forward<Ptr>(ptr)); }


        /** A setter by default constructor */
        template <typename Derived = BaseT> void set_default() {
            this->set_move(std::move(make_derived_shared<BaseT, Derived>()));
        }

        /** A setter by copy constructor */
        template <typename Derived = BaseT> void set_copy(const Derived &t) {
            this->set_move(std::move(make_derived_shared<BaseT, Derived>(t)));
        }

        /** A setter by move constructor */
        template <typename Derived = BaseT> void set_move(Derived &&t) {
            this->set_move(
                std::move(make_derived_shared<BaseT, Derived>(std::forward<Derived>(t))));
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
            this->set_move(std::move(std::make_shared<BaseT>(args...)));
        }

        /** A setter by emplacement with args passed by const reference
         *  The general definition
         */
        template <typename Derived, typename... Args>
        void set_emplace_ref_args(const Args &...args) {
            this->set_move(std::move(make_derived_shared<BaseT, Derived>(args...)));
        }


        /** A setter by emplacement with args passed by forward reference
         *  A specialization that requires no Derived parameter
         */
        template <typename... Args> void set_emplace_foward_args(Args &&...args) {
            this->set_move(std::move(std::make_shared<BaseT>(std::forward<Args>(args)...)));
        }

        /** A setter by emplacement with args passed by forward reference
         *  The general definition
         */
        template <typename Derived, typename... Args>
        void set_emplace_forward_args(Args &&...args) {
            this->set_move(
                std::move(make_derived_shared<BaseT, Derived>(std::forward<Args>(args)...)));
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

} // namespace Utils::ThreadSafe

#endif
