/**
 * @file
 * \ingroup util
 * @brief This file defines a noexcept method to convert an integer type to a string hex.
 */
#ifndef R_SRC_UTIL_TOHEX_HPP_
#define R_SRC_UTIL_TOHEX_HPP_

#include <climits>
#include <string>
#include <type_traits>


namespace Util {

    /** Returns the maximum length string that to_hex_buf can generate given type T
     * '0x' + 2 characters per byte, each representing a nibble + null terminator
     */
    template <typename T> static const constexpr std::size_t to_hex_max_len { 3 + 2 * sizeof(T) };

    /** A noexcept method of converting a T into a lowercase hex string
     *  Stores the resulting string in buf
     *  Warning: This method assumes buf is large enough to hold the string!
     *  Returns the number of bytes stored in buf, not including the null terminator
     */
    template <typename T> inline std::size_t to_hex(const T val, char *const buf) noexcept {
        static_assert(std::is_integral_v<T>, "This will not work on non-integral types");
        static_assert(CHAR_BIT % 2 == 0, "CHAR_BIT is not even");
        static const constexpr char syms[] = "0123456789abcdef"; // NOLINT
        // Prefix
        buf[0] = '0';
        buf[1] = 'x';
        if (val == 0) {
            buf[2] = '0';
            buf[3] = '\0';
            return 3;
        }
        // Body
        std::size_t str_i { 2 };
        const constexpr std::size_t delta { CHAR_BIT / 2 };
        for (std::size_t shft { CHAR_BIT * sizeof(T) - delta }; (shft + delta) != 0;
             shft -= delta) {
            const char next { syms[(val >> shft) & 0xf] };
            if (next != '0' || str_i > 2) {
                buf[str_i] = next;
                str_i += 1;
            }
        }
        // Suffix
        buf[str_i] = '\0';
        return str_i;
    }

    /** A noexcept method of converting a T into a lowercase hex string
     *  If string allocation throws an exception, just crash
     */
    template <typename T> inline std::string to_hex(const T val) noexcept {
        std::string ret(to_hex_max_len<T>, 0); // () not {}
        ret.resize(to_hex(val, ret.data()));
        return ret;
    }

} // namespace Util

#endif
