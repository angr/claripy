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


// Note: These are *not* in the namespace intentionally


#define M_DEFINE_BINARY_CONST_CONST_OP(OP)                                                         \
    /** Define the given operator for the type Enum if it is requested */                          \
    template <typename Enum, std::enable_if_t<Util::BitMask::Private::enabled<Enum>, int> = 0>     \
    constexpr Enum operator OP(const Enum l, const Enum r) {                                       \
        using namespace Util;                                                                      \
        static_assert(Type::Is::strong_enum<Enum>, "Enum is not a scoped enum");                   \
        return static_cast<Enum>(to_underlying(l) OP to_underlying(r));                            \
    }

#define M_DEFINE_BINARY_EQ_OP(OP)                                                                  \
    /** Define the given operator for the type Enum if it is requested */                          \
    template <typename Enum, std::enable_if_t<Util::BitMask::Private::enabled<Enum>, int> = 0>     \
    constexpr Enum operator OP(const Enum l, const Enum r) {                                       \
        using namespace Util;                                                                      \
        static_assert(Type::Is::strong_enum<Enum>, "Enum is not a scoped enum");                   \
        return l = static_cast<Enum>(to_underlying(l) OP to_underlying(r));                        \
    }

// Bitmask operators
M_DEFINE_BINARY_CONST_CONST_OP(|)
M_DEFINE_BINARY_CONST_CONST_OP(&)
M_DEFINE_BINARY_CONST_CONST_OP(^)
M_DEFINE_BINARY_EQ_OP(|=)
M_DEFINE_BINARY_EQ_OP(&=)
M_DEFINE_BINARY_EQ_OP(^=)

#undef M_DEFINE_BINARY_CONST_CONST_OP
#undef M_DEFINE_BINARY_EQ_OP

/** Conditionally enabled ~ bitmask operator */
template <typename Enum, std::enable_if_t<Util::BitMask::Private::enabled<Enum>, int> = 0>
constexpr Enum operator~(const Enum e) {
    using namespace Util;
    static_assert(Type::Is::strong_enum<Enum>, "Enum is not a scoped enum");
    return static_cast<Enum>(~to_underlying(e));
}

#endif
