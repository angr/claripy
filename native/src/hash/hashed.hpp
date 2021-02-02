/**
 * @file
 * @brief This file defines a type that stores a hash value
 */
#ifndef __HASH_HASHED_HPP__
#define __HASH_HASHED_HPP__

#include "type.hpp"

#include "../macros.hpp"


namespace Hash {

    /** A type that has a precomputed hash value */
    struct Hashed {

        /** A hash for this object */
        const Hash hash;

      protected:
        /** Default constructor */
        explicit inline Hashed(const Hash &h) : hash(h) {}

        // Rule of 5
        // This shouldn't be necessary, but better safe than sorry
        SET_IMPLICITS_NONDEFAULT_CTORS(Hashed, default)
        SET_IMPLICITS_OPERATORS(Hashed, delete)
    };

} // namespace Hash

#endif
