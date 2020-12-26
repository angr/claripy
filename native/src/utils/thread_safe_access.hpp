/**
 * @file
 * @brief This file defines the ThreadSafeAccess class
 */
#ifndef __UTILS_THREADSAFEACCESS_HPP__
#define __UTILS_THREADSAFEACCESS_HPP__

#include "../macros.hpp"

#include <algorithm>
#include <memory>
#include <mutex>
#include <type_traits>


namespace Utils {

    /** A class that exposes thread-safe setters and getters for a T
     *  Warning: This does not protect T internally; it only protects setting and getting
     */
    template <typename T> class ThreadSafeAccess {
      public:
        /** The get-able type */
        using Type = std::shared_ptr<T>;

        /** Construct and point to nothing by default */
        ThreadSafeAccess() : obj(nullptr) {}

        /** A getter */
        Type get() const {
            std::shared_lock<decltype(this->m)>(this->m);
            return this->obj;
        }

        /************************************************/
        /*                   Setters                    */
        /************************************************/

        /** A setter that takes in a shared pointer of type type */
        void set_shared_ptr(Type ptr) { this->set(ptr); }

        /** A setter by default constructor */
        void set_default() { this->set(new T); }

        /** A setter by copy constructor */
        template <typename U> void set_copy(const U &t) { this->set(new U(t)); }

        /** A setter by move constructor */
        template <typename U> void set_copy(U &&t) { this->set(new U(t)); }

        /** A setter by emplacement with args passed by copy */
        template <typename U, typename... Args> void set_emplace_ref_copy(Args... args) {
            this->set(new U(std::forward<Args>(args)...));
        }

        /** A setter by emplacement with args passed by reference */
        template <typename U, typename... Args> void set_emplace_ref_args(Args &...args) {
            this->set(new U(args...));
        }

        /** A setter by emplacement with args passed by move */
        template <typename U, typename... Args> void set_emplace_move_args(Args &&...args) {
            this->set(new U(std::forward<Args>(args)...));
        }

      private:
        /** A private member used to set m safely */
        void set(Type ptr) {
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
        std::shared_mutex m;

        /** The object protected by this class */
        Type obj;
    };

} // namespace Utils

#endif
