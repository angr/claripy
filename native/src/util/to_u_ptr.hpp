/**
 * @file
 * \ingroup util
 * @brief This file defines to_u_ref which tries to coerce objects into a UInt reference
 */
#ifndef R_UTIL_TOUPTR_HPP_
#define R_UTIL_TOUPTR_HPP_

#include "dependent_constant.hpp"
#include "ref.hpp"
#include "to_underlying.hpp"
#include "type.hpp"

#include "../constants.hpp"

namespace Util {
    /** Try to coerce x to a UInt */
    template <auto In> constexpr const UInt *to_u_ptr() {
        using T = decltype(In);
        if constexpr (Util::Type::Is::strong_enum<T>) {
            return &ref<UInt, Util::to_underlying(In)>;
        }
        else if constexpr (std::is_convertible_v<T, UInt>) {
            return &ref<UInt, static_cast<UInt>(In)>;
        }
        else {
            static_assert(Util::TD::false_<T>, "Cannot convert T to UInt");
        }
    }
} // namespace Util

#endif
