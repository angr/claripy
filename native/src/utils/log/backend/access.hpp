/**
 * @file
 * \ingroup utils
 * @brief This file methods for accessing the Log Backend
 * The methods within this file are threadsafe
 */
#ifndef __UTILS_LOG_BACKEND_ACCESS_HPP__
#define __UTILS_LOG_BACKEND_ACCESS_HPP__

#include "../../make_derived_shared.hpp"

#include <memory>


namespace Utils::Log::Backend {

    // Forward declarations
    struct Base;

    namespace Private {

        /** Define a private set method */
        void set(std::shared_ptr<Base> &&ptr);

    } // namespace Private

    /** Set the Log Backend to a new T constructed with arguments: args	*/
    template <typename T, typename... Args> inline void set(Args &&...args) {
        static_assert(std::is_base_of_v<Base, T>, "T must subclass log backend Base");
        Private::set(std::move(make_derived_shared<Base, T>(std::forward<Args>(args)...)));
    }

    /** Set the Log Backend to a new T copy constructed from c */
    template <typename T, typename... Args> inline void copy(const T &c) {
        static_assert(std::is_base_of_v<Base, T>, "T must subclass log backend Base");
        std::shared_ptr<Base> ptr(new T(c));
        Private::set(std::move(make_derived_shared<Base, T>(c)));
    }

    /** Return a copy of the Backend */
    std::shared_ptr<Base> get();

} // namespace Utils::Log::Backend

#endif
