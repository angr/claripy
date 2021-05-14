/**
 * @file
 * \ingroup utils
 * @brief An implementation of C++23's std::is_scoped_enum
 */
#ifndef R_UTILS_ISSTRONGENUM_HPP_
#define R_UTILS_ISSTRONGENUM_HPP_

#include "macros.hpp"

#include <type_traits>


namespace Utils {

    namespace Private {

        /** Determine if T is a strong enum: default false case
         *  We implicitly leverage SFINAE here
         */
        template <typename T, bool = std::is_enum_v<T>>
        struct IsStrongEnum final : std::false_type {};

        /** Determine if T is a strong enum: possible true case
         *  We implicitly leverage SFINAE here
         */
        template <typename T>
        struct IsStrongEnum<T, true> final :
            std::bool_constant<!std::is_convertible_v<T, std::underlying_type_t<T>>> {};

    } // namespace Private

    /** True if T is a strong enum */
    template <typename T> UTILS_ICCBOOL is_strong_enum { Private::IsStrongEnum<T>::value };

} // namespace Utils

#endif
