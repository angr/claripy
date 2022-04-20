/**
 * @file
 * \ingroup util
 * @brief This file defines Util::sign and Util::unsign
 */
#ifndef R_SRC_UTIL_SIGN_HPP_
#define R_SRC_UTIL_SIGN_HPP_


namespace Util {

    /** Sign x */
    template <typename T, bool AllowNop = false> constexpr inline auto sign(T x) {
        static_assert(AllowNop || std::is_unsigned_v<T>, "T must be unsigned");
        static_assert(std::is_integral_v<T>, "T must be a primitive");
        return static_cast<std::make_signed_t<T>>(x);
    }

    /** Unsign x */
    template <typename T, bool AllowNop = false> constexpr inline auto unsign(T x) {
        static_assert(AllowNop || std::is_signed_v<T>, "T must be unsigned");
        static_assert(std::is_integral_v<T>, "T must be a primitive");
        return static_cast<std::make_unsigned_t<T>>(x);
    }

} // namespace Util

#endif
