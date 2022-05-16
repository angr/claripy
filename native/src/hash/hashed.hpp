/**
 * @file
 * @brief This file defines a type that stores a hash value
 */
#ifndef R_SRC_HASH_HASHED_HPP_
#define R_SRC_HASH_HASHED_HPP_

#include "constants.hpp"

#include "../macros.hpp"


namespace Hash {

    /** A type that has a precomputed hash value
     *  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!
     */
    struct Hashed {
        /** A hash for this object */
        const Hash hash;

      protected:
        /** Constructor */
        explicit constexpr Hashed(const Hash &h) noexcept : hash { h } {}
        /** Prevent most slicing */
        inline ~Hashed() noexcept = default;
        // Rule of 5
        DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(Hashed);
    };

} // namespace Hash

#endif
