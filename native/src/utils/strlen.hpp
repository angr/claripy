/**
 * @file
 * \ingroup utils
 * @brief This file defines a constexpr strlen
 */
#ifndef R_UTILS_STRLEN_HPP_
#define R_UTILS_STRLEN_HPP_

#include "../constants.hpp"


namespace Utils {

    /** constexpr strlen */
    constexpr UInt strlen(CCSC s) noexcept {
        if (s[0] == 0) {
            return 0;
        }
        else {
            return 1 + strlen(&s[1]);
        }
    }

} // namespace Utils

#endif
