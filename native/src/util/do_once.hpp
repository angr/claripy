/**
 * @file
 * \ingroup util
 * @brief This file defines a method which asserts a condition, and if false throws an exception
 * We use the word affirm since C libraries like to define assert as a macro
 */
#ifndef R_SRC_UTIL_DOONCE_HPP_
#define R_SRC_UTIL_DOONCE_HPP_

#include <atomic>

/** A macro that ensures X will be run only once using type static TYPE as the bool type */
#define UTIL_DOONCE_TYPE(X, TYPE)                                                                  \
    {                                                                                              \
        static TYPE todo { true };                                                                 \
        if (todo) {                                                                                \
            X;                                                                                     \
            todo = false;                                                                          \
        }                                                                                          \
    }

/** A macro that ensures X will be run only once */
#define UTIL_DOONCE(X) UTIL_DOONCE_TYPE(X, bool)

/** A macro that ensures X will be run only once; uses an atomic bool */
#define UTIL_ATOMIC_DOONCE(X) UTIL_DOONCE_TYPE(X, std::atomic_bool)

#endif
