/**
 * @file
 * @brief This file defines a type that stores a hash value
 */
#ifndef R_SRC_HASH_HASHED_HPP_
#define R_SRC_HASH_HASHED_HPP_

#include "type.hpp"

#include "../macros.hpp"


namespace Hash {

    /** A type that has a precomputed hash value */
    struct Hashed {

        /** A hash for this object */
        const Hash hash;

      protected:
        /** Constructor */
        explicit constexpr Hashed(const Hash &h) noexcept : hash { h } {}

        /** Pure virtual destructor */
        virtual inline ~Hashed() noexcept = 0;

        // Rule of 5
        DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(Hashed);
    };

    /** Default virtual destructor */
    Hashed::~Hashed() noexcept = default;

} // namespace Hash

#endif
