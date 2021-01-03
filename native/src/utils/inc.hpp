/**
 * @file
 * \ingroup utils
 * @brief This file contains declares the Utils:inc() function
 */
#ifndef __UTILS_INC_HPP__
#define __UTILS_INC_HPP__

#include "../constants.hpp"

#include <mutex>


namespace Utils {

    /** Thread-safe-ly increment a static number and return the result
     *  The template Args are used as a map key to allow this function to be reused as needed
     *  This function is primarily meant to run before main to help configure things
     */
    template <typename... Args> Constants::UInt inc() {
        static std::mutex m;
        static Constants::UInt ret = 0;
        std::unique_lock<decltype(m)> lock(m);
        return ++ret;
    }

} // namespace Utils

#endif
