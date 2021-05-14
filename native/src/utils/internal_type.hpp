/**
 * @file
 * \ingroup utils
 * @brief This file defines a method which returns U given T<U>
 */
#ifndef R_UTILS_INTERNALTYPE_HPP_
#define R_UTILS_INTERNALTYPE_HPP_

#include "type_to_type.hpp"

#include "../constants.hpp"

#include <type_traits>


namespace Utils {

    namespace Private {
        /** Returns a U given a TypeToType<U>
         *  If we were to simply return U we may lose qualifiers
         */
        template <template <typename> typename T, typename U> TypeToType<U> internal_type(T<U>);
    } // namespace Private

    /** Returns U given T<U> */
    template <typename T>
    using InternalType = typename decltype(Private::internal_type(std::declval<T>()))::Type;

} // namespace Utils

#endif
