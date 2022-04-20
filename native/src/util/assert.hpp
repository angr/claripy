/**
 * @file
 * \ingroup util
 * @brief This file defines a macro which asserts a condition, and if false throws an exception
 */
#ifndef R_SRC_UTIL_ASSERT_HPP_
#define R_SRC_UTIL_ASSERT_HPP_

#include "throw.hpp"


/** A convenient assertion, msg = WHOAMI
 *  We do this instead of a function to keep stack traces clean and reduce binary sizes
 */
#define UTIL_ASSERT_EMPTY(E_TYPE, COND)                                                            \
    {                                                                                              \
        if (UNLIKELY(!(COND))) {                                                                   \
            UTIL_THROW_EMPTY(E_TYPE);                                                              \
        }                                                                                          \
    }

/** A convenient assertion, prepends WHOAMI to ...
 *  We do this instead of a function to keep stack traces clean and reduce binary sizes
 */
#define UTIL_ASSERT(E_TYPE, COND, ...)                                                             \
    {                                                                                              \
        if (UNLIKELY(!(COND))) {                                                                   \
            UTIL_THROW(E_TYPE, __VA_ARGS__);                                                       \
        }                                                                                          \
    }


#endif