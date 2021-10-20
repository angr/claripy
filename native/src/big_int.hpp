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
    /** The type of the value when represented as an int */
    using Int = boost::multiprecision::mpz_int;
    /** The type of the value when represented as a string */
    using Str = std::string;
    /** The type of the value */
    using Value = std::variant<Int, Str>;

    /** Writes value to the ostream */
    inline void write_value(std::ostream &os) const {
        if (std::holds_alternative<BigInt::Int>(value)) {
            os << std::get<BigInt::Int>(value);
        }
        else {
            os << '"' << std::get<BigInt::Str>(value) << '"';
        }
    }

    /** The value */
    Value value;
    /** The bit length */
    UInt bit_length;
};

/** Ostream overload for BigInt */
inline std::ostream &operator<<(std::ostream &os, const BigInt &b) {
    os << "BigInt{";
    b.write_value(os);
    return os << ", " << b.bit_length << "}";
}

/** Equality operator */
inline bool operator==(const BigInt &a, const BigInt &b) {
    return (a.bit_length == b.bit_length) && (a.value == b.value);
}


#endif
