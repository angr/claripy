/**
 * @file
 * \ingroup utils
 * @brief This file defines a function that allows Utils::to_ostringstream handle strong enums
 * It does not affect strong enums with the << stream operator defined
 * Fundamentally this function is just a fancy static_cast
 */
#ifndef __UTILS_PRIVATE_OSTREAMHELPERCONVERSIONS_HPP__
#define __UTILS_PRIVATE_OSTREAMHELPERCONVERSIONS_HPP__

#include "../../macros.hpp"
#include "../is_same.hpp"
#include "../unique.hpp"

#include <ostream>
#include <type_traits>


namespace Utils::Private {

    /** Determine if T is a strong enum: default false case
     *  We implicitly leverage SFINAE here
     */
    template <typename T, bool = std::is_enum_v<T>> struct IsStrongEnum : std::false_type {};

    /** Determine if T is a strong enum: possible true case
     *  We implicitly leverage SFINAE here
     */
    template <typename T>
    struct IsStrongEnum<T, true> :
        std::bool_constant<!std::is_convertible_v<T, std::underlying_type_t<T>>> {};


    /** A struct used to determine if T has the << operator defined */
    template <typename T> struct HasStreamOp {
        UTILS_DEFINE_UNIQUE
        /** If U has the << operator defined the return type is resolvable
         *  Note: we do not use declval for the ostream because some compilers are buggy with it
         *  @todo Update to use declval when possible
         */
        template <typename U>
        static constexpr decltype(*static_cast<std::ostream *>(nullptr) << std::declval<U>())
        test(U *);
        /** If the first declaration had an unresolvable return type, we return a Unique */
        template <typename> static constexpr Unique test(...);
        /** Determine the return type of test<T>(nullptr) */
        using Ret = decltype(test<T>(nullptr));
        /** Compare the return type to determine if the << operator is defined */
        static UTILS_CCBOOL value { !is_exactly_same<Unique, Ret> };
    };


    /** True if and only if T is a strong enum with no << operator defined */
    template <typename T>
    UTILS_ICCBOOL needs_ostream_conversion { IsStrongEnum<T>::value && !HasStreamOp<T>::value };


    /** If T is a strong enum with no stream operator defined, static cast to its underlying type
     */
    template <typename T, std::enable_if_t<needs_ostream_conversion<T>, int> = 0>
    [[gnu::always_inline]] constexpr std::underlying_type_t<T>
    ostream_helper_conversions(const T &v) noexcept {
        return static_cast<std::underlying_type_t<T>>(v);
    }

    /** This specalization is a no-op */
    template <typename T, std::enable_if_t<!needs_ostream_conversion<T>, int> = 0>
    [[gnu::always_inline]] constexpr T &ostream_helper_conversions(T &t) noexcept {
        return t;
    }

} // namespace Utils::Private

#endif
