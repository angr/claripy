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

        /** A hash for this object
         * @todo: add const
         */
        Hash hash;

      protected:
        // Protect construction
        SET_IMPLICITS(Hashed, default)
    };

} // namespace Hash

#endif
