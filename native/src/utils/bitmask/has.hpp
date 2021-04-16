/**
 * @file
 * \ingroup utils
 * @brief Used to verify if an enum has requested flags set
 */
#ifndef __UTILS_BITMASK_HAS_HPP__
#define __UTILS_BITMASK_HAS_HPP__

#include "../../macros.hpp"

#include <type_traits>


namespace Utils::BitMask {

    /** Return true if e has all flags in flags set */
    template <typename Enum> constexpr bool has(const Enum e, const Enum flags) {
        return static_cast<std::underlying_type_t<Enum>>(e & flags) != 0;
    }

} // namespace Utils::BitMask

#endif
