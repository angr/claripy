/**
 * @file
 * @brief This file defines a class that has a const size
 */
#ifndef R_SRC_BITLENGTH_HPP_
#define R_SRC_BITLENGTH_HPP_

#include "constants.hpp"
#include "macros.hpp"


/** A class with a const bit length */
struct BitLength {
  public:
    /** The size */
    const U64 bit_length;

    /** The number of bits in a byte */
    static inline const constexpr U64 char_bit { CHAR_BIT };

  protected:
    /** Protected constructor */
    explicit inline BitLength(const U64 bl) noexcept : bit_length { bl } {}

    /** Virtual destructor */
    virtual inline ~BitLength() noexcept = 0;

    // Rule of 5
    DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(BitLength);
};

/** Default virtual destructor */
BitLength::~BitLength() noexcept = default;


#endif
