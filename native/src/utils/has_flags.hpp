/**
 * @file
 * \ingroup utils
 * @brief Used to verify if an enum has requested flags set
 */
#ifndef __UTILS_HASFLAGS_HPP__
#define __UTILS_HASFLAGS_HPP__

#include "../macros.hpp"

#include <type_traits>


namespace Utils {

    /** Return true if e has all flags in flags set */
    template <typename Enum> constexpr bool has_flag(const Enum e, const Enum flags) {
        return static_cast<std::underlying_type_t<Enum>>(e & flags) != 0;
    }

} // namespace Utils

#endif
