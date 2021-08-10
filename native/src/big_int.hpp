/**
 * @file
 * @brief This defines big integer types
 */
#ifndef R_BIGINT_HPP_
#define R_BIGINT_HPP_

#include <ostream>

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

/** Ostream overload for BigInt */
inline std::ostream &operator<<(std::ostream &os, const BigInt &b) {
    os << "BigInt{" << b.value << ", " << b.bit_length << "}";
    return os;
}

#endif
