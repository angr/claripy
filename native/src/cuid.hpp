/**
 * @file
 * @brief This file defines a type that has a unique class id
 * This file also defines a macro to create a static_cuid
 */
#ifndef __CUID_HPP__
#define __CUID_HPP__

#include "constants.hpp"
#include "macros.hpp"
#include "utils.hpp"


/** Used to define a static_cuid in a class
 *  Leaves the class in a public state
 */
#define DEFINE_STATIC_CUID                                                                        \
  public:                                                                                         \
    /** Define a static_cuid */                                                                   \
    static const constexpr Constants::UInt static_cuid = UTILS_FILE_LINE_HASH;


/** A type that has a class unique id
 *  This has the benefits of a virtual function as inhereted classes
 *  can have different CUIDs than their ancestors, while also avoiding
 *  the overhead of a vtabel call to invoke virtual cuid() const;
 */
struct CUID {

    /** The class unique id */
    const Constants::UInt cuid;

  protected:
    /** Constructor */
    explicit inline CUID(const Constants::UInt c) noexcept : cuid { c } {}

    /** Virtual destructor */
    virtual inline ~CUID() noexcept;

    // Rule of 5
    SET_IMPLICITS_CONST_MEMBERS(CUID, default, noexcept)
};

/** Default virtual destructor */
CUID::~CUID() noexcept = default;


#endif
