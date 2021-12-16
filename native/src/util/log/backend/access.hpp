/**
 * @file
 * \ingroup util
 * @brief This file methods for accessing the Log Backend
 * The methods within this file are threadsafe
 */
#ifndef R_UTIL_LOG_BACKEND_ACCESS_HPP_
#define R_UTIL_LOG_BACKEND_ACCESS_HPP_

#include "../../make_derived_shared.hpp"

#include <memory>


namespace Util::Log::Backend {

    // Forward declarations
    struct Base;

    /** Define a private set method
     *  Warning: Because the logging system is so critical, ensure that all other
     *  copies of ptr do not edit the internals of *ptr in dangerous ways
     *  ptr cannot be nullptr
     *  If silent, internal logging will be limited
     */
    void unsafe_set(std::shared_ptr<const Base> &&ptr, const bool silent);

    /** Set the Log Backend to a new T constructed with arguments: args
     *  If Silent, internal logging will be limited
     */
    template <typename T, bool Silent, typename... Args> inline void set(Args &&...args) {
        static_assert(Type::Is::ancestor<Base, T>, "T must subclass log backend Base");
        unsafe_set(make_derived_shared<const Base, T>(std::forward<Args>(args)...), Silent);
    }

    /** Set the Log Backend to a new T constructed with arguments: args	*/
    template <typename T, typename... Args> inline void set(Args &&...args) {
        set<T, false, Args...>(std::forward<Args>(args)...);
    }

    /** Set the Log Backend to a new T copy constructed from c */
    template <typename T, typename... Args> inline void copy(const T &c) {
        static_assert(Type::Is::ancestor<Base, T>, "T must subclass log backend Base");
        unsafe_set(std::move(make_derived_shared<const Base, T>(c)));
    }

    /** Return a copy of the Backend */
    std::shared_ptr<const Base> get();

} // namespace Util::Log::Backend

#endif
