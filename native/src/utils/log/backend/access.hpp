/**
 * @file
 * @brief This file methods for accessing the Log Backend
 */
#ifndef __UTILS_LOG_BACKEND_ACCESS_HPP__
#define __UTILS_LOG_BACKEND_ACCESS_HPP__

#include "abstract_base.hpp"

#include <memory>


namespace Utils::Log::Backend {

    namespace Private {

        /** Set the Log backend */
        void set(std::shared_ptr<AbstractBase> &&b);

    } // namespace Private

    /** Set the Log backend to a new T constructed with arguments: args */
    template <typename T, typename... Args> void set(const Args &...args) {
        Private::set(std::shared_ptr<AbstractBase>(new T(args...)));
    }

    /** Return a copy of the backend */
    std::shared_ptr<AbstractBase> get();

} // namespace Utils::Log::Backend

#endif
