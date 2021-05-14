/**
 * @file
 * \ingroup utils
 * @brief This file defines to_underlying
 * We use the word affirm since C libraries like to define assert as a macro
 */
#ifndef R_UTILS_TOUNDERLYING_HPP_
#define R_UTILS_TOUNDERLYING_HPP_

#include "is_strong_enum.hpp"


namespace Utils {

    /** Convert e to its underlying type */
    template <typename E> constexpr std::underlying_type_t<E> to_underlying(const E e) noexcept {
        static_assert(std::is_enum_v<E>, "Requires E be an enum");
        static_assert(is_strong_enum<E>, "Strong enums are preferred to weak enums");
        return static_cast<std::underlying_type_t<E>>(e);
    }

} // namespace Utils

#endif
