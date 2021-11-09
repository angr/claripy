/**
 * @file
 * \ingroup util
 * @brief This file defines a macro which uses a common SFINAE trick
 * to determine if some condition is met by its template arguments
 */
#ifndef R_UTIL_SFINAETEST_HPP_
#define R_UTIL_SFINAETEST_HPP_

#include "is_same.hpp"


/** This macro allows easy SFINAE testing of a specified condition
 *  The macro defines a class named CLASS_NAME which uses SFINAE to test CONDITION
 *  This macro defines a constexpr boolean WRAPPER_NAME which can be used to obtain
 *  the whether or not CONDITION was resolvable and valid.
 *  The template arguments the condition requires must be passed in after condition
 *  Note: The first template argument *must* exist and be named T
 *  Note: In the CONDITION use U instead of T as we have to redeclare it as U
 */
#define UTIL_SFINAETEST(WRAPPER_NAME, CLASS_NAME, CONDITION, ...)                                  \
    template <__VA_ARGS__> class CLASS_NAME final {                                                \
        /** Define a unique class */                                                               \
        struct Unique {};                                                                          \
                                                                                                   \
        /** This overload returns a T if CONDITION is resolvable and valid */                      \
        template <typename U> static constexpr decltype(CONDITION) test(U *);                      \
                                                                                                   \
        /** Otherwise we choose this overload, that returns a Unique */                            \
        template <typename> static constexpr Unique test(...);                                     \
                                                                                                   \
        /** The return type of whichever version of test the compiler selects                      \
         *  The compiler will attempt to use the closest matching overload                         \
         *  Our wildcard overload will be attempted last, so our condition test                    \
         *  will be attempted first. If the condition is resolvable and valid,                     \
         *  the first overload will be selected, otherwise the wildcard overload will              \
         */                                                                                        \
        using Ret = decltype(test<T>(nullptr));                                                    \
                                                                                                   \
      public:                                                                                      \
        /** Compare the return types to determine if the condition was resolvable and valid */     \
        static UTIL_CCBOOL value { !Util::is_exactly_same<Unique, Ret> };                          \
    };                                                                                             \
                                                                                                   \
    /** A shortcut for running the SFINAE test and checking the result                             \
     *  Note: this wrapper accepts any arguments it relies on the associated class to type check.  \
     */                                                                                            \
    template <typename... Args> UTIL_ICCBOOL WRAPPER_NAME { CLASS_NAME<Args...>::value };

#endif
