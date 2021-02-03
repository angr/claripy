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
        explicit constexpr Hashed(const Hash &h) noexcept : hash { h } {}

        /** Pure virtual destructor */
        virtual inline ~Hashed() noexcept = 0;

        // Rule of 5
        SET_IMPLICITS_CONST_MEMBERS(Hashed, default, noexcept)
    };

    /** Default virtual destructor */
    Hashed::~Hashed() noexcept = default;

} // namespace Hash

#endif
