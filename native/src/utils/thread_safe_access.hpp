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


namespace Utils {

    /** A class that exposes thread-safe setters and getters for a T
     *  Warning: This does not protect T internally; it only protects setting and getting
     */
    template <typename T> class ThreadSafeAccess {
      public:
        /** Construct and point to nothing by default */
        ThreadSafeAccess() : obj(nullptr) {}

        /** A getter */
        std::shared_ptr<T> get() const {
            std::shared_lock<decltype(this->m)>(this->m);
            return this->obj;
        }

        /************************************************/
        /*                   Setters                    */
        /************************************************/

        /** A setter by default constructor */
        void set_default() { this->set(new T); }

        /** A setter by copy constructor */
        void set_copy(const T &t) { this->set(new T(t)); }

        /** A setter by move constructor */
        void set_copy(T &&t) { this->set(new T(t)); }

        /** A setter by emplacement with args passed by copy */
        template <typename... Args> void set_emplace_ref_copy(Args... args) {
            this->set(new T(std::forward<Args>(args)...));
        }

        /** A setter by emplacement with args passed by reference */
        template <typename... Args> void set_emplace_ref_args(const Args &...args) {
            this->set(new T(args...));
        }

        /** A setter by emplacement with args passed by move */
        template <typename... Args> void set_emplace_move_args(Args &&...args) {
            this->set(new T(std::forward<Args>(args)...));
        }

      private:
        /** A private member used to set m safely */
        void set(T *const o) {
            std::unique_lock<decltype(this->m)>(this->m);
            this->obj.set(o);
        }

        /** A mutex to protect obj */
        std::shared_mutex m;

        /** The object protected by this class */
        std::shared_ptr<T> obj;
    };

} // namespace Utils

#endif
