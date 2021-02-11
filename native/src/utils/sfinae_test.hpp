/**
 * @file
 * \ingroup utils
 * @brief This file defines a macro which uses a common SFINAE trick
 * to determine if some condition is met by its template arguments
 */
#ifndef __UTILS_SFINAETEST_HPP__
#define __UTILS_SFINAETEST_HPP__

#include "is_same.hpp"


#define UTILS_SFINAETEST(WRAPPER_NAME, CLASS_NAME, CONDITION, ...)                                \
    template <__VA_ARGS__> class CLASS_NAME final {                                               \
        /** Define a unique class */                                                              \
        struct Unique {};                                                                         \
                                                                                                  \
        /** This overload returns a T and is resolvable if CONDITION is valid */                  \
        template <typename U> static constexpr decltype(CONDITION) test(U *);                     \
                                                                                                  \
        /** Otherwise we choose this overload, that returns a Unique */                           \
        template <typename> static constexpr Unique test(...);                                    \
                                                                                                  \
        /** The return type of whichever version of test the compiler selects */                  \
        using Ret = decltype(test<T>(nullptr));                                                   \
                                                                                                  \
      public:                                                                                     \
        /** Compare the return types to determine if CONDITION was resolvable and valid */        \
        static UTILS_CCBOOL value { !Utils::is_exactly_same<Unique, Ret> };                       \
    };                                                                                            \
                                                                                                  \
    /** A shortcut for running the SFINAE test and checking the result */                         \
    template <typename... Args> UTILS_ICCBOOL WRAPPER_NAME { CLASS_NAME<Args...>::value };

#endif
