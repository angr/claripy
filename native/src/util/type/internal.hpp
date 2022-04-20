/**
 * @file
 * \ingroup util
 * @brief This file defines a method which returns U given T<U>
 */
#ifndef R_SRC_UTIL_TYPE_INTERNAL_HPP_
#define R_SRC_UTIL_TYPE_INTERNAL_HPP_

#include "to_type.hpp"

#include "../../constants.hpp"


namespace Util::Type {

    namespace Private {
        /** Returns a U given a T<U>
         *  Note: If we were to simply return U we may lose qualifiers
         */
        template <template <typename> typename T, typename U> ToType<U> internal(T<U>);
    } // namespace Private

    /** Returns U given T<U> */
    template <typename T>
    using Internal = typename decltype(Private::internal(std::declval<T>()))::Type;

} // namespace Util::Type

#endif
