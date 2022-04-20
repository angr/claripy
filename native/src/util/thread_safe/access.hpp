/**
 * @file
 * \ingroup util
 * @brief This file defines the thread-safe Access class similar but different from std::atomic
 */
#ifndef R_SRC_UTIL_THREADSAFE_ACCESS_HPP_
#define R_SRC_UTIL_THREADSAFE_ACCESS_HPP_

#include "base.hpp"

#include "../../macros.hpp"
#include "../checked_static_cast.hpp"
#include "../make_derived_shared.hpp"

#include <algorithm>
#include <memory>
#include <mutex>
#include <shared_mutex>
#include <type_traits>


namespace Util::ThreadSafe {

    /** A class that exposes thread-safe setters and getters for a T
     * Warning: This does not protect T internally; it only protects setting and getting
     * Note: this class is similar to std::atomic, except that unlike atomic,
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
            std::shared_lock<decltype(m)> r(m);
            return obj;
        }

        /** Clear the internals */
        void clear() {
            std::lock_guard<decltype(m)> lg(m);
            obj.reset();
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

        /** Copy assignment */
        Access &operator=(const Access &old) {
            if (this != &old) {
                Base::operator=(checked_static_cast<Base>(old));
                set_ref(old.get());
            }
            return *this;
        }

        /** Destructor */
        ~Access() noexcept final = default;

        /** Disable Move constructor */
        Access(Access &&old) = delete;

        /** Disable move assignment */
        Access &operator=(Access &&old) = delete;

        /************************************************/
        /*                   Setters                    */
        /************************************************/

        /** A setter that takes in a shared pointer of type type */
        void set_shared_ptr(const Ptr &ptr) { set_ref(ptr); }

        /** A setter that takes in a shared pointer of type type */
        void set_shared_ptr_move(Ptr &&ptr) { set_move(std::move(ptr)); }

        /** A setter that takes in a shared pointer of type type */
        void set_shared_ptr_swap(Ptr &ptr) { set_swap(ptr); }


        /** A setter by default constructor */
        template <typename Derived = BaseT> void set_default() {
            set_move(std::move(make_derived_shared<BaseT, Derived>()));
        }

        /** A setter by copy constructor */
        template <typename Derived = BaseT> void set_copy(const Derived &t) {
            set_move(std::move(make_derived_shared<BaseT, Derived>(t)));
        }

        /** A setter by move constructor */
        template <typename Derived = BaseT> void set_move(Derived &&t) {
            set_move(std::move(make_derived_shared<BaseT, Derived>(std::move(t))));
        }


        /** A setter by emplacement with args passed by copy
         *  A specialization that requires no Derived parameter
         */
        template <typename... Args> void set_emplace_ref_copy(Args... args) {
            set_emplace_forward_args(std::forward<Args>(args)...);
        }

        /** A setter by emplacement with args passed by copy
         *  The general definition
         */
        template <typename Derived, typename... Args> void set_emplace_ref_copy(Args... args) {
            set_emplace_forward_args<Derived>(std::forward<Args>(args)...);
        }


        /** A setter by emplacement with args passed by const reference
         *  A specialization that requires no Derived parameter
         */
        template <typename... Args> void set_emplace_ref_args(const Args &...args) {
            set_move(std::move(std::make_shared<BaseT>(args...)));
        }

        /** A setter by emplacement with args passed by const reference
         *  The general definition
         */
        template <typename Derived, typename... Args>
        void set_emplace_ref_args(const Args &...args) {
            set_move(std::move(make_derived_shared<BaseT, Derived>(args...)));
        }


        /** A setter by emplacement with args passed by forward reference
         *  A specialization that requires no Derived parameter
         */
        template <typename... Args> void set_emplace_foward_args(Args &&...args) {
            set_move(std::move(std::make_shared<BaseT>(std::forward<Args>(args)...)));
        }

        /** A setter by emplacement with args passed by forward reference
         *  The general definition
         */
        template <typename Derived, typename... Args>
        void set_emplace_forward_args(Args &&...args) {
            set_move(std::move(make_derived_shared<BaseT, Derived>(std::forward<Args>(args)...)));
        }

      private:
        /** A private member used to set m safely */
        inline void set_ref(const Ptr &ptr) {
            std::lock_guard<decltype(m)> lg(m);
            obj = ptr;
        }

        /** A private member used to set m safely*/
        inline void set_move(Ptr &&ptr) {
            std::lock_guard<decltype(m)> lg(m);
            obj = std::move(ptr);
        }

        /** A private member used to set m safely*/
        inline void set_swap(Ptr &ptr) {
            std::lock_guard<decltype(m)> lg(m);
            std::swap(obj, ptr);
        }

        /** A mutex to protect obj */
        mutable std::shared_mutex m;

        /** The object protected by this class */
        Ptr obj { nullptr };
    };

} // namespace Util::ThreadSafe

#endif
