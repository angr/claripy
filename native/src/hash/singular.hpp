/**
 * @file
 * @brief This file defines the underling hash function for Expressions
 */
#ifndef R_HASH_SINGULAR_HPP_
#define R_HASH_SINGULAR_HPP_

#include "hashed.hpp"
#include "type.hpp"

#include "../mode.hpp"
#include "../utils.hpp"

#include <exception>
#include <memory>
#include <string>
#include <type_traits>
#include <vector>


namespace Hash {

    /** Converts its input into a Hash
     *  Since this may be a no-op or very quick we inline full specializations
     *  Every type requries a specialization or is not supported!
     *  Note: we want to avoid inter-type hash collisions so we often xor with a file line hash
     */
    template <typename T> constexpr Hash singular(const T &) noexcept {
        static_assert(Utils::TD::false_<T>,
                      "Given value of T is not supported for Hash::singular");
        return std::declval<Hash>(); // Satisfy the compiler
    }

    /** The FNV1a hash function to be invoked for for size sizeof(Hash) */
    template <typename Type> constexpr auto fnv1a { Utils::FNV1a<Type>::template hash<Hash> };

    /**************************************************/
    /*           Primitive Specializations            */
    /**************************************************/

    /** A specialization for T = char */
    template <> constexpr Hash singular(const char &c) noexcept {
        return UTILS_FILE_LINE_HASH ^ static_cast<Hash>(c);
    }

    /** A specialization for T = float
     *  \todo: For C++20 look into std::bit_cast to make this constexpr
     */
    template <> inline Hash singular(const float &f) noexcept {
        static_assert(sizeof(float) == sizeof(uint32_t),
                      "Numeric type must have the same size as float");
        uint32_t tmp; // NOLINT
        UTILS_TYPE_PUN_ONTO(uint32_t, &tmp, &f, false);
        return UTILS_FILE_LINE_HASH ^ tmp;
    }

    /** A specialization for T = double
     *  \todo: For C++20 look into std::bit_cast to make this constexpr
     */
    template <> inline Hash singular(const double &d) noexcept {
        Hash tmp; // NOLINT
        UTILS_TYPE_PUN_ONTO(Hash, &tmp, &d, false);
        return UTILS_FILE_LINE_HASH ^ tmp;
    }

    /** A specialization for T = bool */
    template <> constexpr Hash singular(const bool &b) noexcept {
        return UTILS_FILE_LINE_HASH ^ (b ? 1ULL : 0ULL);
    }

    /** A specialization for T = Mode::FP */
    template <> constexpr Hash singular(const Mode::FP &m) noexcept {
        using U = std::underlying_type_t<Mode::FP>;
        static_assert(sizeof(m) <= sizeof(Hash), "singular(Mode::FP) must be modified");
        static_assert(std::is_fundamental_v<U> && std::is_fundamental_v<Hash>,
                      "singular(Mode::FP) must be modified");
        return UTILS_FILE_LINE_HASH ^ static_cast<Hash>(Utils::to_underlying(m));
    }

    /** A specialization for T = Constants::CCSC */
    template <> constexpr Hash singular(Constants::CCSC &s) noexcept {
        return UTILS_FILE_LINE_HASH ^ fnv1a<char>(s, Utils::strlen(s));
    }

    /** A specialization for T = Constants::Int */
    template <> constexpr Hash singular(const Constants::Int &i) noexcept {
        static_assert(sizeof(Constants::Int) == sizeof(Hash),
                      "singular(Constants::Int) must be modified");
        static_assert(std::is_fundamental_v<Hash>, "singular(Constants::Int) must be modified");
        // Unsafe for numerical reasons if Hash is unsigned. But we only
        // care about uniqueness, so this is fine if the above hold
        return UTILS_FILE_LINE_HASH ^ static_cast<Hash>(i);
    }

    /** A specialization for T = char[] */
    template <std::size_t N> constexpr Hash singular(const char (&s)[N]) noexcept { // NOLINT
        return UTILS_FILE_LINE_HASH ^ fnv1a<char>(s, N);
    }

    /** A specialization for T = Constants::UInt */
    template <> constexpr Hash singular(const Constants::UInt &i) noexcept {
        // Compiler will warn if this is unsafe or invalid
        return UTILS_FILE_LINE_HASH ^ i;
    }

    /**************************************************/
    /*                Specializations                 */
    /**************************************************/

    /** A specialization for T = std::string */
    template <> inline Hash singular(const std::string &s) noexcept {
        return UTILS_FILE_LINE_HASH ^ fnv1a<char>(s.c_str(), s.size());
    }

    /** A specialization for shared pointers to pre-hashed types */
    template <> inline Hash singular(const std::shared_ptr<const Hashed> &h) noexcept {
        if (h == nullptr) {
            return UTILS_FILE_LINE_HASH;
        }
        // Will warn if types are different or implicit convesion is dangerous / impossible
        return h->hash;
    }

    /** A specialization for shared pointers of strict subclasses of Hashed types */
    template <typename Internal,
              // Require to prevent infinite recursion
              std::enable_if_t<!Utils::is_wrap_same<Hashed, Internal, std::remove_cv_t>, int> = 0,
              // Ensure Internal derives from Hashed
              std::enable_if_t<Utils::is_ancestor<Hashed, Internal>, int> = 0> // Allows primitives
    inline Hash singular(const std::shared_ptr<const Internal> &h) noexcept {
        // Will warn if types are different or implicit convesion is dangerous / impossible
        return singular(Utils::up_cast<Hashed>(h));
    }

    /** A specialization for T = std::vector<Internal> */
    template <typename Internal> inline Hash singular(const std::vector<Internal> &v) noexcept {
        Constants::UInt hashes[v.size()]; // NOLINT
        Constants::UInt i = -1ULL;
        for (const auto &p : v) {
            hashes[++i] = singular(p);
        }
#ifdef DEBUG
        // Verify no memory corruption
        Utils::affirm<Utils::Error::Unexpected::Unknown>(v.size() == i + 1, WHOAMI_WITH_SOURCE
                                                         "Incorrect value of i within Hash::hash");
#endif
        // Return hash
        return fnv1a<Constants::UInt>(hashes, v.size());
    }

} // namespace Hash

#endif
