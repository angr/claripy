/**
 * @file
 * \ingroup util
 * @brief This file defines a macro to affirm something is not nullptr when DEBUG is defined
 */
#ifndef R_SRC_UTIL_ASSERTNOTNULLDEBUG_HPP_
#define R_SRC_UTIL_ASSERTNOTNULLDEBUG_HPP_

#include "assert.hpp"
#include "err.hpp"


#ifdef DEBUG

    /** A macro that null checks (X) iff DEBUG is defined */
    #define UTIL_ASSERT_NOT_NULL_DEBUG(X)                                                          \
        UTIL_ASSERT(::Util::Err::Null, (X) != nullptr, "Nullptr detected.");

#else

    /** A macro that nullchecks (X) iff DEBUG is defined */
    #define UTIL_ASSERT_NOT_NULL_DEBUG(X)

#endif

#endif
