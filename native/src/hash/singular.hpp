/**
 * @file
 * @brief This file defines the underling hash function for Expressions
 */
#ifndef __HASH_SINGULAR_HPP__
#define __HASH_SINGULAR_HPP__

#include "hashed.hpp"
#include "type.hpp"

#include "../utils.hpp"

#include <exception>
#include <memory>
#include <string>
#include <type_traits>
#include <vector>


namespace Hash {

    /** Converts its input into a Hash
     *  Note: these do not have to be unique to all hashes, however
     *  this function called on various inputs should avoid collsions
     *  This function exists to convert its input into Hash that will
     *  later be hashed by a more secure hash function along with other arguments
     *  For example, one use case of this function could be:
     *  array = { singular(expression1), singular(name_string) }; return md5(array);
     *  Since, for numeric types among others, this may be a no-op or very quick, we inline
     * specializations Note: Otherwise full specializations are put in a cpp file and linked later.
     *  Every type requries a specialization or is not supported!
     */
    template <typename T> constexpr Hash singular(const T &) noexcept {
        /* static_assert(false, "Given value of T is not supported for Hash::singular"); */
        static_assert(Utils::TD::false_<T>,
                      "Given value of T is not supported for Hash::singular");
        return std::declval<Hash>(); // Satisfy the compiler
    }

    /** The FNV1a hash function to be invoked for for size sizeof(Hash) */
    template <typename Type>
    const constexpr auto fnv1a { Utils::FNV1a<Type>::template hash<Hash> };

    // Specialization

    /** A specialization for pre-hashed types
     *  Not constexpr
     */
    template <> inline Hash singular(const std::shared_ptr<Hashed> &h) noexcept {
        // Will warn if types are different or implicit convesion is dangerous / impossible
        return h->hash;
    }

    /** A specialization for shared pointers of subclasses of Hashed types
     *  Not constexpr
     */
    template <typename Internal, std::enable_if_t<std::is_base_of_v<Hashed, Internal>, int> = 0>
    inline Hash singular(const std::shared_ptr<Internal> &h) noexcept {
        // Will warn if types are different or implicit convesion is dangerous / impossible
        return singular(std::static_pointer_cast<Hashed>(h));
    }

    /** A specialization for T = Constants::CCSC */
    template <> constexpr inline Hash singular(Constants::CCSC &s) noexcept {
        return fnv1a<char>(s, Utils::strlen(s));
    }

    /** A specialization for T = std::string
     *  Not constexpr
     */
    template <> inline Hash singular(const std::string &s) noexcept {
        return fnv1a<char>(s.c_str(), s.size());
    }

    /** A specialization for T = Constants::Int */
    template <> constexpr inline Hash singular(const Constants::Int &i) noexcept {
        static_assert(sizeof(Constants::Int) == sizeof(Hash),
                      "singular(Constants::Int) must be modified");
        static_assert(std::is_fundamental_v<Hash>, "singular(Constants::Int) must be modified");
        // Unsafe for numerical reasons if Hash is unsigned. But we only
        // care about uniqueness, so this is fine if the above hold
        return static_cast<Hash>(i);
    }

    /** A specialization for T = Constants::UInt */
    template <> constexpr inline Hash singular(const Constants::UInt &i) noexcept {
        // Compiler will warn if this is unsafe or invalid
        return i;
    }

    /** A specialization for T = std::vector<Internal>
     *  Not constexpr
     */
    template <typename Internal> inline Hash singular(const std::vector<Internal> &v) noexcept {
        Constants::UInt hashes[v.size()]; // NOLINT
        Constants::UInt i = -1ULL;
        for (const auto &p : v) {
            hashes[++i] = singular(p);
        }
#ifdef DEBUG
        // Verify no memory corruption
        Utils::affirm<Utils::Error::Unexpected::Unknown>(v.size() == i,
                                                         "Incorrect value of i within Hash::hash");
#endif
        // Return hash
        return fnv1a<Constants::UInt>(hashes, v.size());
    }

} // namespace Hash

#endif
