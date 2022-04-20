/**
 * @file
 * \ingroup util
 * @brief This file defines underlying
 * We use the word affirm since C libraries like to define assert as a macro
 */
#ifndef R_SRC_UTIL_TOUNDERLYING_HPP_
#define R_SRC_UTIL_TOUNDERLYING_HPP_

#include "type.hpp"


namespace Util {

    /** Convert e to its underlying type */
    template <typename E> constexpr std::underlying_type_t<E> to_underlying(const E e) noexcept {
        static_assert(std::is_enum_v<E>, "Requires E be an enum");
        static_assert(Type::Is::strong_enum<E>, "Strong enums are preferred to weak enums");
        return static_cast<std::underlying_type_t<E>>(e);
    }

} // namespace Util

#endif
