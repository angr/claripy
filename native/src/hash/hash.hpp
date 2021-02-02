/**
 * @file
 * @brief This file defines the hash function
 */
#ifndef __HASH_HASH_HPP__
#define __HASH_HASH_HPP__

#include "singular.hpp"

#include "../utils.hpp"

#include <sstream>
#include <type_traits>
#include <typeinfo>


namespace Hash {

    /** This function hashes it's arguments
     *  Note: types may want to pass in some sort of typeid if their hashes matter
     */
    template <typename... Args> constexpr Hash hash(const Args &...args) {
        constexpr Constants::UInt size = sizeof...(Args);
        Constants::UInt hashes[size]; // NOLINT
        Constants::UInt i { -1ULL };
        // Basically: hashes[i] = singular(args[i]) for each arg
        (static_cast<void>(hashes[++i] = singular(args)), ...);
#if DEBUG
        // Verify no memory corruption
        Utils::affirm<Utils::Error::Unexpected::Unknown>(size == i,
                                                         "Incorrect value of i within Hash::hash");
#endif
        // Return hash
        using Hasher = Utils::FNV1a<Hash>; // The type being hashed is Hash
        // Since Hash is a fundamental numeric type, we specify the size as Hash
        return Hasher::hash<Hash>(hashes, size);
    }

} // namespace Hash

#endif
