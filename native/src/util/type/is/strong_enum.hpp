/**
 * @file
 * \ingroup util
 * @brief An implementation of C++23's std::is_scoped_enum
 */
#ifndef R_SRC_UTIL_TYPE_IS_STRONGENUM_HPP_
#define R_SRC_UTIL_TYPE_IS_STRONGENUM_HPP_

#include "../../macros.hpp"

#include <type_traits>


namespace Util::Type::Is {

    namespace Private {

        /** Determine if T is a strong enum: default false case
         *  We implicitly leverage SFINAE here
         */
        template <typename T, bool = std::is_enum_v<T>>
        struct StrongEnum final : std::false_type {};

        /** Determine if T is a strong enum: possible true case
         *  We implicitly leverage SFINAE here
         */
        template <typename T>
        struct StrongEnum<T, true> final :
            std::bool_constant<not std::is_convertible_v<T, std::underlying_type_t<T>>> {};

    } // namespace Private

    /** True if T is a strong enum */
    template <typename T> UTIL_ICCBOOL strong_enum { Private::StrongEnum<T>::value };

} // namespace Util::Type::Is

#endif
