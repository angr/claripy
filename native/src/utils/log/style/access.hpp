/**
 * @file
 * \ingroup utils
 * @brief This file methods for accessing the Log Style
 * The methods within this file are threadsafe
 */
#ifndef __UTILS_LOG_STYLE_ACCESS_HPP__
#define __UTILS_LOG_STYLE_ACCESS_HPP__

#include <memory>


namespace Utils::Log::Style {

    // Forward declarations
    struct Base;

    namespace Private {

        /** Set the logging style */
        void set(std::shared_ptr<Base> &ptr);

    } // namespace Private

    /** Set the Log Style to a new T constructed with arguments: args */
    template <typename T, typename... Args> inline void set(Args &&...args) {
        static_assert(std::is_base_of_v<Base, T>, "T must subclass log style Base");
        std::shared_ptr<Base> ptr(new T(std::forward<Args>(args)...));
        Private::set(ptr);
    }

    /** Set the Log Style to a new T copy constructed from c */
    template <typename T, typename... Args> inline void copy(const T &c) {
        static_assert(std::is_base_of_v<Base, T>, "T must subclass log style Base");
        std::shared_ptr<Base> ptr(new T(c));
        Private::set(ptr);
    }

    /** Return a copy of the Style */
    std::shared_ptr<Base> get();

} // namespace Utils::Log::Style

#endif
