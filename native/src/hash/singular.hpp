/**
 * @file
 * @brief This file defines the underling hash function for Exprs
 */
#ifndef R_SRC_HASH_SINGULAR_HPP_
#define R_SRC_HASH_SINGULAR_HPP_

#include "hashed.hpp"
#include "type.hpp"

#include "../big_int.hpp"
#include "../mode.hpp"
#include "../util.hpp"

#include <exception>
#include <memory>
#include <string>
#include <type_traits>
#include <vector>


namespace Hash {

    /** Converts its input into a Hash
     *  Since this may be a no-op or very quick we inline full specializations
     *  Every type requires a specialization or is not supported!
     *  Note: we want to avoid inter-type hash collisions so we often xor with a file line hash
     */
    template <typename T> constexpr Hash singular(const T &) noexcept {
        static_assert(Util::TD::false_<T>, "Given value of T is not supported for Hash::singular");
        return std::declval<Hash>(); // Satisfy the compiler
    }

    /** The FNV1a hash function to be invoked for for size sizeof(Hash) */
    template <typename Type> constexpr auto fnv1a { Util::FNV1a<Type>::template hash<Hash> };

    /**************************************************/
    /*           Primitive Specializations            */
    /**************************************************/

    static_assert(sizeof(Hash) >= sizeof(I64), "Hash of unexpected size");

    /** A specialization for T = int8_t */
    template <> constexpr Hash singular(const int8_t &c) noexcept {
        return UTIL_FILE_LINE_HASH ^ static_cast<Hash>(c);
    }

    /** A specialization for T = int16_t */
    template <> constexpr Hash singular(const int16_t &c) noexcept {
        return UTIL_FILE_LINE_HASH ^ static_cast<Hash>(c);
    }

    /** A specialization for T = int32_t */
    template <> constexpr Hash singular(const int32_t &c) noexcept {
        return UTIL_FILE_LINE_HASH ^ static_cast<Hash>(c);
    }

    /** A specialization for T = I64 */
    template <> constexpr Hash singular(const I64 &c) noexcept {
        return UTIL_FILE_LINE_HASH ^ static_cast<Hash>(c);
    }

    /** A specialization for T = uint8_t */
    template <> constexpr Hash singular(const uint8_t &c) noexcept {
        return UTIL_FILE_LINE_HASH ^ static_cast<Hash>(c);
    }

    /** A specialization for T = uint16_t */
    template <> constexpr Hash singular(const uint16_t &c) noexcept {
        return UTIL_FILE_LINE_HASH ^ static_cast<Hash>(c);
    }

    /** A specialization for T = uint32_t */
    template <> constexpr Hash singular(const uint32_t &c) noexcept {
        return UTIL_FILE_LINE_HASH ^ static_cast<Hash>(c);
    }

    /** A specialization for T = U64 */
    template <> constexpr Hash singular(const U64 &c) noexcept {
        return UTIL_FILE_LINE_HASH ^ static_cast<Hash>(c);
    }

    /** A specialization for T = char */
    template <> constexpr Hash singular(const char &c) noexcept {
        return UTIL_FILE_LINE_HASH ^ static_cast<Hash>(c);
    }

    /** A specialization for T = float
     *  @todo: For C++20 look into std::bit_cast to make this constexpr
     */
    template <> inline Hash singular(const float &f) noexcept {
        static_assert(sizeof(float) == sizeof(uint32_t),
                      "Numeric type must have the same size as float");
        uint32_t tmp; // NOLINT
        UTIL_TYPE_PUN_ONTO(&tmp, &f);
        return UTIL_FILE_LINE_HASH ^ tmp;
    }

    /** A specialization for T = double
     *  @todo: For C++20 look into std::bit_cast to make this constexpr
     */
    template <> inline Hash singular(const double &d) noexcept {
        Hash tmp; // NOLINT
        UTIL_TYPE_PUN_ONTO(&tmp, &d);
        return UTIL_FILE_LINE_HASH ^ tmp;
    }

    /** A specialization for T = bool */
    template <> constexpr Hash singular(const bool &b) noexcept {
        return UTIL_FILE_LINE_HASH ^ (b ? 1ULL : 0ULL);
    }

    /** A specialization for T = CCSC */
    template <> constexpr Hash singular(CCSC &s) noexcept {
        return UTIL_FILE_LINE_HASH ^ fnv1a<char>(s, Util::strlen(s));
    }

    /** A specialization for T = char[] */
    template <std::size_t N> constexpr Hash singular(const char (&s)[N]) noexcept { // NOLINT
        return UTIL_FILE_LINE_HASH ^ fnv1a<char>(s, N);
    }

    /**************************************************/
    /*                Specializations                 */
    /**************************************************/

    /** A specialization for T = Mode::FP::Rounding */
    template <> constexpr Hash singular(const Mode::FP::Rounding &m) noexcept {
        using U = std::underlying_type_t<Mode::FP::Rounding>;
        static_assert(sizeof(m) <= sizeof(Hash), "singular(Mode::FP) must be modified");
        static_assert(std::is_fundamental_v<U> && std::is_fundamental_v<Hash>,
                      "singular(Mode::FP::Rounding) must be modified");
        return UTIL_FILE_LINE_HASH ^ static_cast<Hash>(Util::to_underlying(m));
    }

    /** A specialization for T = Mode::FP::Width */
    template <> inline Hash singular(const Mode::FP::Width &w) noexcept {
        static_assert(sizeof(Mode::FP::Width) == 2 * sizeof(uint32_t),
                      "Mode::FP::Width's composition differs from expected");
        static_assert(sizeof(Mode::FP::Width) == sizeof(Hash),
                      "singular(Mode::FP::Width) must be modified.");
        Hash tmp; // NOLINT
        UTIL_TYPE_PUN_ONTO(&tmp, &w);
        return UTIL_FILE_LINE_HASH ^ tmp;
    }

    /** A specialization for T = std::byte */
    template <> constexpr Hash singular(const std::byte &b) noexcept {
        return UTIL_FILE_LINE_HASH ^ static_cast<Hash>(Util::to_underlying(b));
    }

    /** A specialization for T = std::string
     *  @todo: comapre speed to c++ hash for string when size_t is 8 bytes
     */
    template <> inline Hash singular(const std::string &s) noexcept {
        return UTIL_FILE_LINE_HASH ^ fnv1a<char>(s.c_str(), s.size());
    }

    /** A specialization for T = boost::multiprecision::mpz_int */
    template <> inline Hash singular(const BigInt &arb) noexcept {
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
        if (std::holds_alternative<BigInt::Int>(arb.value)) {
            const mpz_t &raw { std::get<BigInt::Int>(arb.value).backend().data() };
            const auto len { Util::widen<mp_limb_t, true>(raw->_mp_size) };
            return UTIL_FILE_LINE_HASH ^ arb.bit_length ^ fnv1a<mp_limb_t>(raw->_mp_d, len);
        }
        else {
            return UTIL_FILE_LINE_HASH ^ singular(std::get<BigInt::Str>(arb.value));
        }
    }

    /** A specialization for shared pointers to pre-hashed types */
    template <> inline Hash singular(const std::shared_ptr<const Hashed> &h) noexcept {
        if (h == nullptr) {
            return UTIL_FILE_LINE_HASH;
        }
        // Will warn if types are different or implicit conversion is dangerous / impossible
        return h->hash;
    }

    /** A specialization for shared pointers of strict subclasses of Hashed types */
    template <
        typename Inner,
        // Require to prevent infinite recursion
        std::enable_if_t<not Util::Type::Is::wrap_same<Hashed, Inner, std::remove_cv_t>, int> = 0,
        // Ensure Inner derives from Hashed
        std::enable_if_t<Util::Type::Is::ancestor<Hashed, Inner>, int> = 0> // Allows prims
    inline Hash singular(const std::shared_ptr<const Inner> &h) noexcept {
        // Will warn if types are different or implicit conversion is dangerous / impossible
        return singular(Util::PCast::Static::up<Hashed>(h));
    }

    /** A specialization for T = std::vector<Inner> */
    template <typename Inner>
    inline Hash singular(const std::vector<Inner> &v) NOEXCEPT_UNLESS_DEBUG {
        U64 hashes[v.size()]; // NOLINT
        U64 i { -1_ui };
        for (const auto &p : v) {
            hashes[++i] = singular(p);
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
