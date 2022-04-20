/**
 * @file
 * \ingroup util
 * @brief This file defines operators which enable enums to become bitmasks
 */
#ifndef R_SRC_UTIL_BITMASK_OPERATORS_HPP_
#define R_SRC_UTIL_BITMASK_OPERATORS_HPP_

#include "enable.hpp"

#include "../../macros.hpp"
#include "../to_underlying.hpp"
#include "../type.hpp"

// These are *not* in the namespace intentionally

/** A local macro used to define a binary operator that does not edit anything */
#define DEFINE_BINARY_CONST_CONST_OP(OP)                                                           \
    /** Define the given operator for the type Enum if it is requested */                          \
    template <typename Enum, std::enable_if_t<Util::BitMask::Private::enabled<Enum>, int> = 0>     \
    constexpr Enum operator OP(const Enum l, const Enum r) {                                       \
        using namespace Util;                                                                      \
        static_assert(Type::Is::strong_enum<Enum>, "Enum is not a scoped enum");                   \
        return static_cast<Enum>(to_underlying(l) OP to_underlying(r));                            \
    }

/** A local macro used to define a binary eq operator */
#define DEFINE_BINARY_EQ_OP(OP)                                                                    \
    /** Define the given operator for the type Enum if it is requested */                          \
    template <typename Enum, std::enable_if_t<Util::BitMask::Private::enabled<Enum>, int> = 0>     \
    constexpr Enum operator OP(const Enum l, const Enum r) {                                       \
        using namespace Util;                                                                      \
        static_assert(Type::Is::strong_enum<Enum>, "Enum is not a scoped enum");                   \
        return l = static_cast<Enum>(to_underlying(l) OP to_underlying(r));                        \
    }

// Bitmask operators
DEFINE_BINARY_CONST_CONST_OP(|)
DEFINE_BINARY_CONST_CONST_OP(&)
DEFINE_BINARY_CONST_CONST_OP(^)
DEFINE_BINARY_EQ_OP(|=)
DEFINE_BINARY_EQ_OP(&=)
DEFINE_BINARY_EQ_OP(^=)

/** Conditionally enabled ~ bitmask operator */
template <typename Enum, std::enable_if_t<Util::BitMask::Private::enabled<Enum>, int> = 0>
constexpr Enum operator~(const Enum e) {
    using namespace Util;
    static_assert(Type::Is::strong_enum<Enum>, "Enum is not a scoped enum");
    return static_cast<Enum>(~to_underlying(e));
}

// Cleanup
#undef DEFINE_BINARY_CONST_CONST_OP
#undef DEFINE_BINARY_EQ_OP

#endif
