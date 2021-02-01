/**
 * @file
 * \ingroup utils
 * @brief This file defines a constexpr strlen
 */
#ifndef __UTILS_STRLEN_HPP__
#define __UTILS_STRLEN_HPP__

#include "../constants.hpp"


namespace Utils {

    /** constexpr strlen */
    constexpr Constants::UInt strlen(Constants::CCSC s) {
        if (s[0] == 0) {
            return 0;
        }
        else {
            return 1 + strlen(&s[1]);
        }
    }

} // namespace Utils

#endif
