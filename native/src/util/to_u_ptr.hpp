/**
 * @file
 * \ingroup util
 * @brief This file defines to_u_ref which tries to coerce objects into a U64 reference
 */
#ifndef R_SRC_UTIL_TOUPTR_HPP_
#define R_SRC_UTIL_TOUPTR_HPP_

#include "dependent_constant.hpp"
#include "ref.hpp"
#include "to_underlying.hpp"
#include "type.hpp"

#include "../constants.hpp"

namespace Util {
    /** Try to coerce In to a U64 */
    template <auto In> constexpr const U64 *to_u_ptr() {
        using T = decltype(In);
        if constexpr (Util::Type::Is::strong_enum<T>) {
            return &ref<U64, Util::to_underlying(In)>;
        }
        else if constexpr (std::is_convertible_v<T, U64>) {
            return &ref<U64, static_cast<U64>(In)>;
        }
        else {
            static_assert(Util::TD::false_<T>, "Cannot convert T to U64");
        }
    }
} // namespace Util

#endif
