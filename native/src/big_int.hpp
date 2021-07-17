/**
 * @file
 * @brief This defines big integer types
 */
#ifndef R_BIGINT_HPP_
#define R_BIGINT_HPP_

#include <boost/multiprecision/gmp.hpp>


/** The arbitrary precision type claricpp uses */
struct BigInt {

    /** The type of the value */
    using Value = boost::multiprecision::mpz_int;

    /** The value */
    Value value;

    /** The bit length */
    Constants::UInt bit_length;
};

#endif
