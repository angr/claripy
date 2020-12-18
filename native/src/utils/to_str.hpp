/**
 * @file
 * @brief This file defines Utils::to_str
 */
#ifndef __UTILS_TOSTR_HPP__
#define __UTILS_TOSTR_HPP__

#include "private/to_str.hpp"

#include <sstream>


/** A namespace used for the utils directory */
namespace Utils {

    /** This function takes in a set of arguments, and returns a string that comprises them
     *  Each argument must have the << stream operator defined
     */
    template <typename... Args> std::string to_str(const Args... args) {
        std::stringstream s;
        Private::to_str(s, std::forward<const Args>(args)...);
        return s.str();
    }

} // namespace Utils

#endif
