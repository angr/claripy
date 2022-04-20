/**
 * @file
 * \ingroup util
 * @brief This file defines hex_to_int
 */
#ifndef R_SRC_UTIL_HEXTONUM_HPP_
#define R_SRC_UTIL_HEXTONUM_HPP_

#include <cstdint>
#include <limits>


namespace Util {

    /** Returns the value the hex character represents
     *  If h is not in [0-9a-zA-Z] return's max value
     */
    constexpr inline uint8_t hex_to_num(const char h) noexcept {
        using U8 = uint8_t;
        if (h >= '0' && h <= '9') {
            return static_cast<U8>(h - '0');
        }
        else if (h >= 'a' && h <= 'f') {
            return static_cast<U8>(h - ('a' - char { 10 }));
        }
        else if (h >= 'A' && h <= 'F') {
            return static_cast<U8>(h - ('A' - char { 10 }));
        }
        return std::numeric_limits<U8>::max();
    }

} // namespace Util

#endif
