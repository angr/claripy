/**
 * @file
 * \ingroup utils
 * @brief This file defines a noexcept method to convert an integer type to a string hex.
 */
#ifndef R_UTILS_TOHEX_HPP_
#define R_UTILS_TOHEX_HPP_

#include <string>
#include <type_traits>


namespace Utils {

    /** A noexcept method of converting a T into a hex string */
    template <typename T> inline std::string to_hex(const T val) noexcept {
        static_assert(std::is_integral_v<T>, "This will not work on non-integral types");
        static_assert(sizeof(T) > 0, "T must be sized!");
        static_assert(CHAR_BIT % 2 == 0, "CHAR_BIT is not even");
        // Prep
        static const constexpr char syms[] = "0123456789abcdef"; // NOLINT
        const std::size_t max { 2 + 2 * sizeof(T) };
        std::string ret(max, 0);
        // Convert the value nibble by nibble
        ret[0] = '0';
        ret[1] = 'x';
        std::size_t str_i { 2 };
        const constexpr std::size_t delta { CHAR_BIT / 2 };
        for (std::size_t shft { CHAR_BIT * sizeof(T) - delta }; (shft + delta) != 0;
             shft -= delta) {
            const char next { syms[(val >> shft) & 0xf] };
            if (next != '0' || str_i > 2) {
                ret[str_i] = next;
                str_i += 1;
            }
        }
        ret.resize(str_i);
        return ret;
    }
} // namespace Utils

#endif
