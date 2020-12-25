/**
 * @file
 * @brief This file methods for accessing the Log Style
 */
#ifndef __UTILS_LOG_STYLE_ACCESS_HPP__
#define __UTILS_LOG_STYLE_ACCESS_HPP__

#include "abstract_base.hpp"

#include <memory>


namespace Utils::Log::Style {

    namespace Private {

        /** Set the logging style */
        void set(std::shared_ptr<AbstractBase> &&s);

    } // namespace Private

    /** Set the logging style to a new T constructed with arguments: args */
    template <typename T, typename... Args> void set(const Args &...args) {
        Private::set(std::shared_ptr<AbstractBase>(new T(args...)));
    }

    /** Return a copy of the style */
    std::shared_ptr<AbstractBase> get();

} // namespace Utils::Log::Style

#endif
