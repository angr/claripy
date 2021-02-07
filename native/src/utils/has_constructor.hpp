/**
 * @file
 * \ingroup utils
 * @brief This file defines a way to check if a type T can accepts Args... args.
 * Note: unlike std::is_constructible, this can be friended to allow private constructor access
 */
#ifndef __UTILS_HASCONSTRUCTOR_HPP__
#define __UTILS_HASCONSTRUCTOR_HPP__

#include "is_same.hpp"
#include "unique.hpp"


namespace Utils {

    /** A struct which determines if the constructor T(Args...) is visible and exists
     *  Basically std::is_constructible but can be friendedto allow private constructor access
     */
    template <typename T, typename... Args> struct HasConstructor {
        UTILS_DEFINE_UNIQUE

        /** This overload returns a T and is resolvable if T(Args...) is invokable */
        template <typename U> static constexpr decltype(U(std::declval<Args>()...)) test(U *);
        /** Otherwise we choose this overload, that returns a Unique */
        template <typename> static constexpr Unique test(...);

        /** The return type of the selected overload */
        using Ret = decltype(test<T>(nullptr));
        /** Compare the return types to determine if T(Args...) as resolvable and invokable */
        static UTILS_CCBOOL value { !is_exactly_same<Unique, Ret> };
    };

    /** A shortcut for checking of T(Args...) is visible and exists */
    template <typename T, typename... Args>
    UTILS_ICCBOOL has_constructor { HasConstructor<T, Args...>::value };

} // namespace Utils

#endif
