/**
 * @file
 * @brief This file defines Compare mask
 */
#ifndef R_MODE_COMPARE_HPP_
#define R_MODE_COMPARE_HPP_

#include "../util.hpp"

#include <ostream>


namespace Mode {
    /** A mask used to define the type of comparison to be used */
    enum class Compare { Signed = 1, Unsigned = 2, Less = 4, Greater = 8, Eq = 16, Neq = 32 };
} // namespace Mode

// Enable bit masking
UTIL_BITMASK_ENABLE(Mode::Compare)

namespace Mode {

    /** Return true only if Compare is in a valid state */
    constexpr bool compare_is_valid(const Compare c) {
        namespace B = Util::BitMask;
        using C = Compare;
        return (B::has(c, C::Signed) ^ B::has(c, C::Unsigned)) &&
               (B::has(c, C::Less) ^ B::has(c, C::Greater)) &&
               (B::has(c, C::Eq) ^ B::has(c, C::Neq));
    }

    /** Stream operator */
    inline std::ostream &operator<<(std::ostream &os, const Compare &c) {
        namespace B = Util::BitMask;
        using C = Compare;
        os << "Mode::Compare: ";
        if (LIKELY(compare_is_valid(c))) {
            os << (B::has(c, C::Signed) ? "Signed-" : "Unsigned-");
            os << (B::has(c, C::Less) ? "Less-" : "Greater-");
            os << (B::has(c, C::Eq) ? "Eq" : "Neq");
        }
        else {
            os << "Invalid value: " << Util::to_underlying(c) << ". Flags: " << std::boolalpha
               << "{ Signed: " << B::has(c, C::Signed) << ", Unsigned: " << B::has(c, C::Unsigned)
               << ", Less: " << B::has(c, C::Less) << ", Greater: " << B::has(c, C::Greater)
               << ", Eq: " << B::has(c, C::Eq) << ", Neq: " << B::has(c, C::Neq) << " }";
        }
        return os;
    }

} // namespace Mode

#endif
