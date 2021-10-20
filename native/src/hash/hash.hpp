/**
 * @file
 * @brief This file defines the hash function
 */
#ifndef R_HASH_HASH_HPP_
#define R_HASH_HASH_HPP_

#include "singular.hpp"

#include "../util.hpp"

#include <sstream>
#include <type_traits>
#include <typeinfo>


namespace Hash {

    /** This function hashes it's arguments
     *  Note: types may want to pass in some sort of typeid if their hashes matter
     */
    template <typename... Args> constexpr Hash hash(Args &&...args) {
        constexpr UInt size { sizeof...(Args) };
        static_assert(size > 0, "hash needs arguments");

        // Single item case
        if constexpr (size == 1) {
            return singular(std::forward<Args>(args)...);
        }

        // Variables
        Hash hashes[size]; // NOLINT
        UInt i { -1_ui };

        // Basically: hashes[i] = singular(args[i]) for each arg
        (static_cast<void>(hashes[++i] = singular(std::forward<Args>(args))), ...);

#ifdef DEBUG
        // Verify no memory corruption
        Util::affirm<Util::Err::Unknown>(size == i + 1, WHOAMI_WITH_SOURCE
                                         "Incorrect value of i within Hash::hash");
#endif

        // Return a hash of the array of hashes
        // Since Hash is a fundamental numeric type, we specify the size as Hash
        return Util::FNV1a<Hash>::hash<Hash>(hashes, size);
    }

} // namespace Hash

#endif
