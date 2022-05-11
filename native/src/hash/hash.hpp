/**
 * @file
 * @brief This file defines the hash function
 */
#ifndef R_SRC_HASH_HASH_HPP_
#define R_SRC_HASH_HASH_HPP_

#include "serialize.hpp"
#include "type.hpp"

#include <sstream>
#include <typeinfo>


namespace Hash {

    /** This function hashes it's arguments
     *  Note: types may want to pass in some sort of typeid if their hashes matter
     */
    template <typename... Args> constexpr Hash hash(Args &&...args) {
        constexpr U64 size { 1 + sizeof...(Args) };
        static_assert(size > 1, "hash needs arguments");

        // Variables
        Hash hashes[size]; // NOLINT
        U64 i { 0_ui };

        // A hash for the types of Args with references removed
        hashes[0] = type<Args...>;

        // Basically: hashes[i] = singular(args[i]) for each arg
        (static_cast<void>(hashes[++i] = serialize(std::forward<Args>(args))), ...);

#ifdef DEBUG
        // Verify no memory corruption
        UTIL_ASSERT(Util::Err::Unknown, size == i + 1, "Incorrect value of i within Hash::hash");
#endif

        // Return a hash of the array of hashes
        // Since Hash is a fundamental numeric type, we specify the size as Hash
        return Util::FNV1a<Hash>::hash<Hash>(hashes, size);
    }

} // namespace Hash

#endif
