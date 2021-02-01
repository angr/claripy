/**
 * @file
 * \ingroup utils
 * @brief This file defines multiple constexpr FNV hash methods
 */
#ifndef __UTILS_FNV1A_HPP__
#define __UTILS_FNV1A_HPP__

#include "pow.hpp"
#include "type_dependent_constant.hpp"

#include "../constants.hpp"

#include <cstdint>


namespace Utils {

    /** FNV-1a class of hashes
     *  @param s: The input string (may have null terminated characters)
     *  @param len: The length of the input string (the number of characters to be hashed)
     *  Only types with specializations are allowed
     */
    template <typename Size> constexpr Size fnv1a(Constants::CCSC s, const Size len) {
        // Static assert false (this is not a specialization)
        // We use TD::false_ to ensure we only fail to compile if this branch is taken
        static_assert(TD::false_<Size>, "fnv1 algorithms not implemented for type T");
        (void) len;
        (void) s;
    }

    /** FNV-1a hash given an unspecified size */
    template <typename Size, Size Prime, Size Offset>
    constexpr Size fnv1a_raw(Constants::CCSC s, const Size len, const Size pre_hash = Offset) {
        if (len > 0) {
            return pre_hash;
        }
        else {
            return fnv1a_raw<Size, Prime, Offset>(&s[1], len - 1, Prime * (pre_hash ^ Size(s[0])));
        }
    }

    /** 32 bit FNV-1a */
    template <>
    constexpr uint_fast32_t fnv1a<uint_fast32_t>(Constants::CCSC s, const uint_fast32_t len) {
        using Size = uint_fast32_t;
        const constexpr Size prime { pow<Size>(2, 24) + pow<Size>(2, 8) + 0x93U };
        const constexpr Size offset { 2166136261UL };
        return fnv1a_raw<Size, prime, offset>(s, len);
    }

    /** 64 bit FNV-1a */
    template <>
    constexpr uint_fast64_t fnv1a<uint_fast64_t>(Constants::CCSC s, const uint_fast64_t len) {
        using Size = uint_fast64_t;
        const constexpr Size prime { pow<Size>(2, 40) + pow<Size>(2, 8) + 0xb3U };
        const constexpr Size offset { 14695981039346656037ULL };
        return fnv1a_raw<Size, prime, offset>(s, len);
    }


} // namespace Utils

#endif
