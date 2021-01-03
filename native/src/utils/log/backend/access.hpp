/**
 * @file
 * \ingroup utils
 * @brief This file methods for accessing the Log Backend
 * The methods within this file are threadsafe
 */
#ifndef __UTILS_LOG_BACKEND_ACCESS_HPP__
#define __UTILS_LOG_BACKEND_ACCESS_HPP__

#include "abstract_base.hpp"

#include <memory>


namespace Utils::Log::Backend {

    namespace Private {

        /** Define a private set method */
        void set(std::shared_ptr<AbstractBase> &ptr);

    } // namespace Private

    /** Set the Log Backend to a new T constructed with arguments: args	*/
    template <typename T, typename... Args> void set(Args &...args) {
        std::shared_ptr<AbstractBase> ptr(new T(args...));
        Private::set(ptr);
    }

    /** Set the Log Backend to a new T constructed with arguments: args	*/
    template <typename T, typename... Args> void copy(T &c) {
        static_assert(std::is_base_of_v<AbstractBase, T>, "");
        T *t = new T(c);
        std::shared_ptr<AbstractBase> ptr(t);
        /* std::shared_ptr<AbstractBase> ptr(new T(c)); */
        Private::set(ptr);
    }

    /** Return a copy of the Backend */
    std::shared_ptr<AbstractBase> get();

} // namespace Utils::Log::Backend

#endif
