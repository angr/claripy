/**
 * @file
 * \ingroup utils
 * @brief This file defines multiple constexpr FNV hash methods
 */
#ifndef R_UTILS_FNV1A_HPP_
#define R_UTILS_FNV1A_HPP_

#include "dependent_constant.hpp"
#include "is_same.hpp"
#include "pow.hpp"
#include "unconstructable.hpp"

#include "../constants.hpp"

#include <cstdint>
#include <type_traits>


namespace Utils {

    /** FNV-1a class of hashes */
    template <typename TypeToHash> struct FNV1a final : public Unconstructable {

        /** 32-bit type */
        using u32T = uint32_t;
        /** 64-bit type */
        using u64T = uint64_t;

        /** const Input type */
        using CInput = Constants::CTSC<TypeToHash>;

      private:
        /** FNV-1a hash body */
        template <typename HashSize, HashSize Prime, HashSize Offset>
        static constexpr HashSize internal_hash(CInput s, const HashSize len,
                                                const HashSize pre_hash = Offset) noexcept {
            if (len == 0) { // It is unsafe to dereference s here
                return pre_hash;
            }
            else {
                return internal_hash<HashSize, Prime, Offset>(
                    // Passes an invalid pointer of len == 1 (this is ok because we do not use it
                    // when len = 0
                    &s[1],
                    // len >= 1, so this is safe
                    len - 1,
                    // s[0] is safe since len != 0
                    Prime * (pre_hash ^ static_cast<HashSize>(s[0])));
            }
        }

      public:
        /** 32 bit hash */
        static constexpr u32T u32(CInput s, const u32T len) noexcept {
            const constexpr u32T prime { pow<u32T>(2, 24) + pow<u32T>(2, 8) + 0x93U };
            const constexpr u32T offset { 2166136261UL };
            return internal_hash<u32T, prime, offset>(s, len);
        }

        /** 64-bit hash */
        static constexpr u64T u64(CInput s, const u64T len) noexcept {
            const constexpr u64T prime { pow<u64T>(2, 40) + pow<u64T>(2, 8) + 0xb3U };
            const constexpr u64T offset { 14695981039346656037ULL };
            return internal_hash<u64T, prime, offset>(s, len);
        }

        /** Any HashSize version
         *  Default: Constants::UInt
         */
        template <typename HashSize = Constants::UInt>
        static constexpr Constants::UInt hash(CInput s, const Constants::UInt len) noexcept {
            static_assert(sizeof(HashSize) >= sizeof(TypeToHash),
                          "FNV1a::hash given a size too small for the given TypeToHash");
            if constexpr (is_same_ignore_cv<HashSize, u64T>) {
                return u64(s, len);
            }
            else if constexpr (Utils::is_same_ignore_cv<HashSize, u32T>) {
                return u32(s, len);
            }
            else {
                // Static assert false
                // Use TD::false_ to ensure we only fail if this branch is taken
                static_assert(TD::false_<TypeToHash>,
                              "Hash::FNV1a::hash not implemented for choice of HashSize");
            }
        }
    };

} // namespace Utils

#endif
