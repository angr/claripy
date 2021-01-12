/**
 * @file
 * \ingroup utils
 * @brief This file defines a bool that determines if T has the pre ++ operator defined
 */
#ifndef __UTILS_PRIVATE_HASPREINCOP_HPP__
#define __UTILS_PRIVATE_HASPREINCOP_HPP__

#include "../../constants.hpp"

#include <utility>

namespace Utils::Private {

    /** A struct used to determine if T has the pre ++ operator is defined */
    template <typename T> struct HasPreIncOp {
        /** A forward declaration of a type that doesn't exist anywhere else */
        class Unique;
        /** If U has the << operator defined the return type is resolvable
         *  Note: we do not use declval for the ostream because some compilers are buggy with it
         *  @todo Update to use declval when possible
         */
        template <typename U> static constexpr decltype(++std::declval<U>()) test(U *);
        /** If the first declaration had an unresolvable return type, we return a Unique */
        template <typename U> static constexpr Unique test(...);
        /** Determine the return type of test<T>(nullptr) */
        using Ret = decltype(test<T>(nullptr));
        /** Compare the return type to determine if the << operator is defined */
        static constexpr bool value = !std::is_same<Unique, Ret>::value;
    };

    /** A bool that determines if T has the pre ++ operator is defined */
    template <typename T> constexpr bool has_pre_inc_op = HasPreIncOp<T>::value;

} // namespace Utils::Private

#endif
