/**
 * @file
 * @brief This file hash-serialization methods for C++ types
 * Note: This serialization is not necessarily reversible
 * For example: serialize(Hashed) will return the hash of Hashed
 */
#ifndef R_SRC_HASH_SERIALIZE_HPP_
#define R_SRC_HASH_SERIALIZE_HPP_

#include "constants.hpp"
#include "hashed.hpp"

#include "../big_int.hpp"
#include "../mode.hpp"
#include "../util.hpp"

#include <exception>
#include <memory>
#include <string>
#include <type_traits>
#include <vector>


namespace Hash {

    /** Serialize the input (this process is not necessarily reversible)
     *  For example: serialize(Hashed) will return the hash of Hashed
     *  Since this may be a no-op or very quick we inline full specializations
     *  Every type requires a specialization or is not supported!
     *  Note: we want to avoid inter-type hash collisions so we often xor with a file line hash
     */
    template <typename T> constexpr Hash serialize(const T &) noexcept {
        static_assert(Util::TD::false_<T>, "Given value of T is not supported for Hash::serialize");
        return std::declval<Hash>(); // Satisfy the compiler
    }

    /** A specialization for shared pointers to pre-hashed types
     *  Do not hash a shared pointer of a non-const object
     */
    template <typename T> inline Hash serialize(const std::shared_ptr<T> &) noexcept {
        static_assert(Util::TD::false_<T>, "Shared pointer internals should be const");
        return std::declval<Hash>(); // Satisfy the compiler
    }

    /** The FNV1a hash function to be invoked for for size sizeof(Hash) */
    template <typename Type> constexpr auto fnv1a { Util::FNV1a<Type>::template hash<Hash> };

    /**************************************************/
    /*           Primitive Specializations            */
    /**************************************************/

    static_assert(sizeof(Hash) >= sizeof(I64), "Hash of unexpected size");

    /** A specialization for T = int8_t */
    template <> constexpr Hash serialize(const int8_t &c) noexcept {
        return static_cast<Hash>(c);
    }

    /** A specialization for T = int16_t */
    template <> constexpr Hash serialize(const int16_t &c) noexcept {
        return static_cast<Hash>(c);
    }

    /** A specialization for T = int32_t */
    template <> constexpr Hash serialize(const int32_t &c) noexcept {
        return static_cast<Hash>(c);
    }

    /** A specialization for T = I64 */
    template <> constexpr Hash serialize(const I64 &c) noexcept {
        return static_cast<Hash>(c);
    }

    /** A specialization for T = uint8_t */
    template <> constexpr Hash serialize(const uint8_t &c) noexcept {
        return static_cast<Hash>(c);
    }

    /** A specialization for T = uint16_t */
    template <> constexpr Hash serialize(const uint16_t &c) noexcept {
        return static_cast<Hash>(c);
    }

    /** A specialization for T = uint32_t */
    template <> constexpr Hash serialize(const uint32_t &c) noexcept {
        return static_cast<Hash>(c);
    }

    /** A specialization for T = U64 */
    template <> constexpr Hash serialize(const U64 &c) noexcept {
        return static_cast<Hash>(c);
    }

    /** A specialization for T = char */
    template <> constexpr Hash serialize(const char &c) noexcept {
        return static_cast<Hash>(c);
    }

    /** A specialization for T = float
     *  @todo: For C++20 look into std::bit_cast to make this constexpr
     */
    template <> inline Hash serialize(const float &f) noexcept {
        static_assert(sizeof(float) == sizeof(uint32_t),
                      "Numeric type must have the same size as float");
        uint32_t tmp; // NOLINT
        UTIL_TYPE_PUN_ONTO(&tmp, &f);
        return tmp;
    }

    /** A specialization for T = double
     *  @todo: For C++20 look into std::bit_cast to make this constexpr
     */
    template <> inline Hash serialize(const double &d) noexcept {
        Hash tmp; // NOLINT
        UTIL_TYPE_PUN_ONTO(&tmp, &d);
        return tmp;
    }

    /** A specialization for T = bool */
    template <> constexpr Hash serialize(const bool &b) noexcept {
        return b ? 1ULL : 0ULL;
    }

    /** A specialization for T = CCSC */
    template <> constexpr Hash serialize(CCSC &s) noexcept {
        return fnv1a<char>(s, Util::strlen(s));
    }

    /** A specialization for T = char[] */
    template <std::size_t N> constexpr Hash serialize(const char (&s)[N]) noexcept { // NOLINT
        return fnv1a<char>(s, N);
    }

    /**************************************************/
    /*                Specializations                 */
    /**************************************************/

    /** A specialization for T = Mode::FP::Rounding */
    template <> constexpr Hash serialize(const Mode::FP::Rounding &m) noexcept {
        using U = std::underlying_type_t<Mode::FP::Rounding>;
        static_assert(sizeof(m) <= sizeof(Hash), "serialize(Mode::FP) must be modified");
        static_assert(std::is_fundamental_v<U> && std::is_fundamental_v<Hash>,
                      "serialize(Mode::FP::Rounding) must be modified");
        return static_cast<Hash>(Util::to_underlying(m));
    }

    /** A specialization for T = Mode::FP::Width */
    template <> inline Hash serialize(const Mode::FP::Width &w) noexcept {
        static_assert(sizeof(Mode::FP::Width) == 2 * sizeof(uint32_t),
                      "Mode::FP::Width's composition differs from expected");
        static_assert(sizeof(Mode::FP::Width) == sizeof(Hash),
                      "serialize(Mode::FP::Width) must be modified.");
        Hash tmp; // NOLINT
        UTIL_TYPE_PUN_ONTO(&tmp, &w);
        return tmp;
    }

    /** A specialization for T = std::byte */
    template <> constexpr Hash serialize(const std::byte &b) noexcept {
        return static_cast<Hash>(Util::to_underlying(b));
    }

    /** A specialization for T = std::string
     *  @todo: comapre speed to c++ hash for string when size_t is 8 bytes
     */
    template <> inline Hash serialize(const std::string &s) noexcept {
        return fnv1a<char>(s.c_str(), s.size());
    }

    /** A serialization for BigInt::Value */
    inline Hash serialize_helper(const BigInt::Value &value) noexcept {
        // mp_limb_t is assumed to be a standard integral type, typically unsigned long
        // This basic idea will work for a different type, but the hash will have to
        // be on a char * rather than an mp_limb_t * directly, which would be much slower
        // as it would hash one character at a time rather than one mp_limb_t at a time
        static_assert(std::is_integral_v<mp_limb_t>, "gmp assumptions violated");
        static_assert(std::is_unsigned_v<mp_limb_t>, "gmp assumptions violated");
        // We do not care how BigInt stores its data as long as they
        // represent the same thing we should hash them identically
        // Unfortunately, doing so would require converting on to the other which defeats
        // the purpose of allowing them to be represented as they please... @todo Improve me
        if (std::holds_alternative<BigInt::Int>(value)) {
            const mpz_t &raw { std::get<BigInt::Int>(value).backend().data() };
            const auto len { Util::widen<mp_limb_t, true>(raw->_mp_size) };
            return fnv1a<mp_limb_t>(raw->_mp_d, len);
        }
        else {
            return serialize(std::get<BigInt::Str>(value));
        }
    }

    /** A specialization for T = BigInt */
    template <> inline Hash serialize(const BigInt &arb) noexcept {
        return HASH_CANTOR(serialize_helper(arb.value), arb.bit_length);
    }

    /** A serialization method for pre-hashed types */
    inline Hash serialize_helper(CTSC<Hashed> h) noexcept {
        if (h == nullptr) {
            return 0;
        }
        return h->hash;
    }

    /** A specialization for shared pointers to pre-hashed types */
    template <typename T> inline Hash serialize(const std::shared_ptr<const T> &p) noexcept {
        return serialize_helper(p.get()); // SFINAE reject if not a Hashed
    }

    /** A specialization for std::optional of integral types */
    template <typename T> inline Hash serialize(const std::optional<T> &o) noexcept {
        static_assert(std::is_integral_v<Util::Type::RemoveCVR<T>>, "T must be integral");
        return HASH_CANTOR(Hash { o.has_value() }, serialize(o.value_or(0)));
    }

    /** A specialization for T = std::vector<Inner> */
    template <typename Inner>
    inline Hash serialize(const std::vector<Inner> &v) NOEXCEPT_UNLESS_DEBUG {
        U64 hashes[v.size()]; // NOLINT
        U64 i { -1_ui };
        for (const auto &p : v) {
            hashes[++i] = serialize(p);
        }
#ifdef DEBUG
        // Verify no memory corruption
        UTIL_ASSERT(Util::Err::Unknown, v.size() == i + 1,
                    "Incorrect value of i within Hash::hash");
#endif
        // Return hash
        return fnv1a<U64>(hashes, v.size());
    }

} // namespace Hash

#endif
