/**
 * @file
 * @brief This file contains declares the Utils:inc() function
 */
#ifndef __UTILS_INC_HPP__
#define __UTILS_INC_HPP__

#include "../constants.hpp"

#include <mutex>


namespace Utils {

    /** Thread-safe-ly increment a static number and return the result
     *  The template Args are used as a map key to allow this function to be reused as needed
     */
    template <typename... Args> Constants::Int inc() {
        static std::mutex m;
        static Constants::Int ret = 0;
        std::unique_lock<decltype(m)> lock(m);
        return ++ret;
    }

} // namespace Utils

#endif
