/**
 * @file
 * @brief This file defines a type that stores a hash value
 */
#ifndef R_SRC_HASH_HASHED_HPP_
#define R_SRC_HASH_HASHED_HPP_

#include "type.hpp"

#include "../macros.hpp"


namespace Hash {

    /** A type that has a precomputed hash value
     *  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!
     */
    struct Hashed {
        /** Constructor */
        inline Hashed(const Hash &h) noexcept : hash { h } {}
        /** A hash for this object */
        const Hash hash;

      protected:
        /** Prevent most slicing */
        ~Hashed() noexcept = default;
    };

} // namespace Hash

#endif
