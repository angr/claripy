/**
 * @file
 * @brief This file defines a class that has a const size
 */
#ifndef __CSIZED_HPP__
#define __CSIZED_HPP__

#include "constants.hpp"
#include "macros.hpp"


/** A class with a const size */
struct CSized {
  public:
    /** The size */
    const Constants::UInt size;

  protected:
    /** Protected constructor */
    explicit inline CSized(const Constants::UInt s) noexcept : size { s } {}

    /** Virtual destructor */
    virtual inline ~CSized() noexcept;

    // Rule of 5
    SET_IMPLICITS_CONST_MEMBERS(CSized, default, noexcept)
};

/** Default virtual destructor */
CSized::~CSized() noexcept = default;


#endif
