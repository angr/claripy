/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::sign and Utils::unsign
 */
#ifndef R_UTILS_SIGN_HPP_
#define R_UTILS_SIGN_HPP_


namespace Utils {

    /** Sign x */
    template <typename T> constexpr inline auto sign(T x) {
        static_assert(std::is_integral_v<T>, "T must be a primitive");
        static_assert(std::is_unsigned_v<T>, "T must be unsigned");
        return static_cast<std::make_signed_t<T>>(x);
    }

    /** Unsign x */
    template <typename T> constexpr inline auto unsign(T x) {
        static_assert(std::is_integral_v<T>, "T must be a primitive");
        static_assert(std::is_signed_v<T>, "T must be unsigned");
        return static_cast<std::make_unsigned_t<T>>(x);
    }

} // namespace Utils

#endif
