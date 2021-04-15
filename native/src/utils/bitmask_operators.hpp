/**
 * @file
 * \ingroup utils
 * @brief This file defines operators which enable enums to become bitmasks
 */
#ifndef __UTILS_DEFINE_BITMASK_HPP__
#define __UTILS_DEFINE_BITMASK_HPP__

#include "enable_as_bitmask.hpp"
#include "is_strong_enum.hpp"

#include "../macros.hpp"

#include <type_traits>

// These are *not* in the namespace intentionally

/** A local macro used to define a binary operator that does not edit anything */
#define DEFINE_BINARY_CONST_CONST_OP(OP)                                                          \
    /** Define the given operator for the type Enum if it is requested */                         \
    template <typename Enum, std::enable_if_t<Utils::bitmask_enabled<Enum>, int> = 0>             \
    constexpr Enum operator OP(const Enum l, const Enum r) {                                      \
        static_assert(Utils::is_strong_enum<Enum>, "Enum is not a scoped enum");                  \
        using Underling = typename std::underlying_type_t<Enum>;                                  \
        return static_cast<Enum>(static_cast<Underling>(l) OP static_cast<Underling>(r));         \
    }

/** A local macro used to define a binary eq operator */
#define DEFINE_BINARY_EQ_OP(OP)                                                                   \
    /** Define the given operator for the type Enum if it is requested */                         \
    template <typename Enum, std::enable_if_t<Utils::bitmask_enabled<Enum>, int> = 0>             \
    constexpr Enum operator OP(const Enum l, const Enum r) {                                      \
        static_assert(Utils::is_strong_enum<Enum>, "Enum is not a scoped enum");                  \
        using Underling = typename std::underlying_type_t<Enum>;                                  \
        return l = static_cast<Enum>(static_cast<Underling>(l) OP static_cast<Underling>(r));     \
    }

// Bitmask operators
DEFINE_BINARY_CONST_CONST_OP(|)
DEFINE_BINARY_CONST_CONST_OP(&)
DEFINE_BINARY_CONST_CONST_OP(^)
DEFINE_BINARY_EQ_OP(|=)
DEFINE_BINARY_EQ_OP(&=)
DEFINE_BINARY_EQ_OP(^=)

/** Conditinally enabled ~ bitmask operator */
template <typename Enum, std::enable_if_t<Utils::bitmask_enabled<Enum>, int> = 0>
constexpr Enum operator~(const Enum e) {
    return static_cast<Enum>(~static_cast<std::underlying_type_t<Enum>>(e));
}

// Cleanup
#undef DEFINE_BINARY_CONST_CONST_OP
#undef DEFINE_BINARY_EQ_OP

#endif
