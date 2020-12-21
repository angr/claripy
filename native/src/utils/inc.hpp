/**
 * @file
 * @brief This file contains declares the Utils:inc() function
 */
#ifndef __UTILS_INC_HPP__
#define __UTILS_INC_HPP__

#include "../constants.hpp"


/** A namespace used for the utils directory */
namespace Utils {

    /** Increment a static number and return the result
     *  The template Args are used as a map key to allow this function to be reused as needed
     */
    template <typename... Args> Constants::Int inc() {
        static Constants::Int ret = 0;
        return ++ret;
    }

} // namespace Utils

#endif
