/**
 * @file
 * \ingroup util
 * @brief This file defines a macro which uses a common SFINAE trick
 * to determine if some condition is met by its template arguments
 */
#ifndef R_SRC_UTIL_TYPE_SFINAETEST_HPP_
#define R_SRC_UTIL_TYPE_SFINAETEST_HPP_

#include "unique.hpp"

#include "../macros.hpp"

#include <type_traits>


/** This macro allows easy SFINAE testing of a specified condition
 *  This macro defines a constexpr boolean NAME which can be used to test CONDITION
 *  Template argumnets, which must exist, may be passed in via variadic marco arguments
 */
#define UTIL_TYPE_SFINAETEST(NAME, CONDITION, ...)                                                 \
    /** A struct used to test CONDITION */                                                         \
    struct NAME##_class {                                                                          \
        /** This overload can be used if CONDITION is resolvable and valid */                      \
        template <__VA_ARGS__> static constexpr decltype(CONDITION) test(int);                     \
        /** This overload is low priority but will be a fallback if CONDITION is invalid */        \
        template <typename...> static constexpr ::Util::Type::Unique test(...);                    \
    };                                                                                             \
    /** Determine if CONDITION is resolvable and valid                                             \
     *  Call the NAME##_class test functions.                                                      \
     *  If CONDITION is resolvable and valid, the return type will be decltype(CONDITION).         \
     *  If CONDITION is invalid, the return type will be Unique                                    \
     *  We compare the return types to determine which overload was called.                        \
     *  By doing so we effectively determine if CONDITION is resolvable and valid                  \
     */                                                                                            \
    template <typename... Args>                                                                    \
    static UTIL_CCBOOL NAME {                                                                      \
        !::std::is_same_v<::Util::Type::Unique, decltype(NAME##_class::test<Args...>(0))>          \
    };

#endif
