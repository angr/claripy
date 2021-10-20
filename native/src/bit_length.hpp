/**
 * @file
 * @brief This file defines a class that has a const size
 */
#ifndef R_BITLENGTH_HPP_
#define R_BITLENGTH_HPP_

#include "constants.hpp"
#include "macros.hpp"


/** A class with a const bit length */
struct BitLength {
  public:
    /** The size */
    const UInt bit_length;

    /** The number of bits in a byte */
    static inline const constexpr UInt char_bit { C_CHAR_BIT };

  protected:
    /** Protected constructor */
    explicit inline BitLength(const UInt bl) noexcept : bit_length { bl } {}

    /** Virtual destructor */
    virtual inline ~BitLength() noexcept = 0;

    // Rule of 5
    DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(BitLength);
};

/** Default virtual destructor */
BitLength::~BitLength() noexcept = default;


#endif
