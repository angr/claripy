/**
 * @file
 * \ingroup util
 * @brief This file defines multiple constexpr FNV hash methods
 */
#ifndef R_SRC_UTIL_FNV1A_HPP_
#define R_SRC_UTIL_FNV1A_HPP_

#include "dependent_constant.hpp"
#include "pow.hpp"
#include "type.hpp"

#include "../constants.hpp"

#include <climits>
#include <cstdint>
#include <type_traits>


namespace Util {

    /** FNV-1a class of hashes */
    template <typename TypeToHash> struct FNV1a final : public Type::Unconstructable {

        /** 32-bit type */
        using U32 = uint32_t;
        /** const Input type */
        using CInput = CTSC<TypeToHash>;

      private:
        /** FNV-1a hash body */
        template <typename UInt, UInt Prime, UInt Offset>
        static constexpr UInt internal_hash(CInput s, const UInt len,
                                            const UInt pre_hash = Offset) noexcept {
            if (len == 0) { // It is unsafe to dereference s here
                return pre_hash;
            }
            else {
                return internal_hash<UInt, Prime, Offset>(
                    // When len == 1, passes an invalid pointer.
                    // This is ok because the next step will not dereference it
                    s + 1,
                    // len >= 1, so this is safe
                    len - 1,
                    // s[0] is safe since len != 0
                    Prime * (pre_hash ^ static_cast<UInt>(s[0])));
            }
        }

      public:
        /** 32 bit hash */
        static constexpr U32 u32(CInput s, const U32 len) noexcept {
            const constexpr U32 prime { pow<U32>(2, 24) + pow<U32>(2, 8) + 0x93U };
            const constexpr U32 offset { 2166136261UL };
            return internal_hash<U32, prime, offset>(s, len);
        }

        /** 64-bit hash */
        static constexpr U64 u64(CInput s, const U64 len) noexcept {
            const constexpr U64 prime { pow<U64>(2, 40) + pow<U64>(2, 8) + 0xb3U };
            const constexpr U64 offset { 14695981039346656037ULL };
            return internal_hash<U64, prime, offset>(s, len);
        }

        /** Any HashSize version
         *  Default: 64
         */
        template <U64 HashSize = 64> static constexpr auto hash(CInput s, const U64 len) noexcept {
            static_assert(HashSize >= CHAR_BIT * sizeof(TypeToHash),
                          "FNV1a::hash given a size too small for the given TypeToHash");
            if constexpr (HashSize == 64) {
                return u64(s, len);
            }
            else if constexpr (HashSize == 32) {
                return u32(s, len);
            }
            else {
                // Static assert false
                // Use TD::false_ to ensure we only fail if this branch is taken
                static_assert(TD::false_<TypeToHash>,
                              "Hash::FNV1a::hash not implemented for choice of HashSize");
            }
        }

        /** Any HashUIntT version */
        template <typename HashUIntT>
        static constexpr HashUIntT hash(CInput s, const U64 len) noexcept {
            return hash<sizeof(HashUIntT) * CHAR_BIT>(s, len);
        }
    };

} // namespace Util

#endif
