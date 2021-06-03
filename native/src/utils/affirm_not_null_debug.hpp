/**
 * @file
 * \ingroup utils
 * @brief This file defines a macro to affirm something is not nullptr when DEBUG is defined
 */
#ifndef R_UTILS_AFFIRMNOTNULLDEBUG_HPP_
#define R_UTILS_AFFIRMNOTNULLDEBUG_HPP_

#include "error.hpp"


#ifdef DEBUG

    /** A macro that nullchecks (X) iff DEBUG is defined */
    #define UTILS_AFFIRM_NOT_NULL_DEBUG(X)                                                        \
        if (UNLIKELY((X) == nullptr)) {                                                           \
            throw ::Utils::Error::Unexpected::Null(WHOAMI_WITH_SOURCE "Nullptr detected.");       \
        }

#else

    /** A macro that nullchecks (X) iff DEBUG is defined */
    #define UTILS_AFFIRM_NOT_NULL_DEBUG(X)

#endif

#endif
