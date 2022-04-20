/**
 * @file
 * \ingroup util
 * @brief Used to verify if an enum has requested flags set
 */
#ifndef R_SRC_UTIL_BITMASK_HAS_HPP_
#define R_SRC_UTIL_BITMASK_HAS_HPP_

#include "../../macros.hpp"
#include "../to_underlying.hpp"

#include <type_traits>


namespace Util::BitMask {

    /** Return true if e has all flags in flags set */
    template <typename Enum> constexpr bool has(const Enum e, const Enum flags) {
        const auto tmp { to_underlying(flags) };
        return (to_underlying(e) & tmp) == tmp;
    }

    /** Return true if e has all flags in flags set */
    template <typename Enum> constexpr bool has_any(const Enum e, const Enum flags) {
        return (to_underlying(e) & to_underlying(flags)) != 0;
    }

} // namespace Util::BitMask

#endif
