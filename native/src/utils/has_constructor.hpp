/**
 * @file
 * \ingroup utils
 * @brief This file defines a way to check if a type has a visible constructor matching a specific
 * signature
 */
#ifndef __UTILS_HASCONSTRUCTOR_HPP__
#define __UTILS_HASCONSTRUCTOR_HPP__

#include "unique.hpp"


namespace Utils {

    /** A struct which determines if the constructor T(Args...) is visible and exists */
    template <typename T, typename... Args> struct HasConstructor {
        UTILS_DEFINE_UNIQUE

        /** This overload returns a T and is resolvable if T(Args...) is invokable */
        template <typename U> static constexpr decltype(U(std::declval<Args>()...)) test(U *);
        /** Otherwise we choose this overload, that returns a Unique */
        template <typename> static constexpr Unique test(...);

        /** The return type of the selected overload */
        using Ret = decltype(test<T>(nullptr));
        /** Compare the return types to determine if T(Args...) as resolvable and invokable */
        static constexpr bool value { !std::is_same_v<Unique, Ret> };
    };

    /** A shortcut for checking of T(Args...) is visible and exists */
    template <typename T, typename... Args>
    const constexpr bool has_constructor { HasConstructor<T, Args...>::value };

} // namespace Utils

#endif
