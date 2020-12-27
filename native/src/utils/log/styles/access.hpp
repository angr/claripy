/**
 * @file
 * @brief This file methods for accessing the Log Style
 * The methods within this file are threadsafe
 */
#ifndef __UTILS_LOG_STYLE_ACCESS_HPP__
#define __UTILS_LOG_STYLE_ACCESS_HPP__

#include "abstract_base.hpp"

#include <memory>


namespace Utils::Log::Style {

    namespace Private {

        /** Set the logging style */
        void set(std::shared_ptr<AbstractBase> &ptr);

    } // namespace Private

    /** Set the Log Style to a new T constructed with arguments: args */
    template <typename T, typename... Args> void set(Args &...args) {
        std::shared_ptr<AbstractBase> ptr(new T(args...));
        Private::set(ptr);
    }

    /** Return a copy of the Style */
    std::shared_ptr<AbstractBase> get();

} // namespace Utils::Log::Style

#endif
