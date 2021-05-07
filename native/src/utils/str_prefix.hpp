/**
 * @file
 * \ingroup utils
 * @brief This file defines the str_prefix function
 */
#ifndef __UTILS_STRPREFIX_HPP__
#define __UTILS_STRPREFIX_HPP__

#include "strlen.hpp"


namespace Utils {

    /** Return true if a starts with b */
    constexpr bool str_prefix(Constants::CCS a, Constants::CCS b) {
        if (Utils::strlen(a) < Utils::strlen(b)) {
            return false;
        }
        for (; *b; ++a, ++b) {
            if (*a != *b) {
                return false;
            }
        }
        return true;
    }
} // namespace Utils

#endif
