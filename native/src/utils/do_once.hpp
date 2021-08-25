/**
 * @file
 * \ingroup utils
 * @brief This file defines a method which asserts a condition, and if false throws an exception
 * We use the word affirm since C libraries like to define assert as a macro
 */
#ifndef R_UTILS_DOONCE_HPP_
#define R_UTILS_DOONCE_HPP_

/** A macro that ensures X will be run only once */
#define UTILS_DOONCE(X)                                                                           \
    {                                                                                             \
        static bool todo { true };                                                                \
        if (todo) {                                                                               \
            X;                                                                                    \
            todo = false;                                                                         \
        }                                                                                         \
    }

#endif
