/**
 * @file
 * @brief This file defines constants used by Hash
 */
#ifndef R_SRC_HASH_CONSTANTS_HPP_
#define R_SRC_HASH_CONSTANTS_HPP_

#include "../constants.hpp"


/** Define a small hash function for 2 integers */
#define HASH_CANTOR(A, B) (((A) + (B)) / 2 * ((A) + (B) + 1) + (B))


namespace Hash {
    /** The Hash type
     *  Guaranteed to be never throw
     */
    using Hash = U64;
} // namespace Hash

#endif
