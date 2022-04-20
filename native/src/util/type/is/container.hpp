/**
 * @file
 * \ingroup util
 * @brief Defines container and related functions
 */
#ifndef R_SRC_UTIL_TYPE_IS_CONTAINER_HPP_
#define R_SRC_UTIL_TYPE_IS_CONTAINER_HPP_

#include <memory>
#include <type_traits>


namespace Util::Type::Is {

    namespace Private {
        /** Returns true if T is a shared pointer */
        template <template <typename...> typename, typename> struct IsC : std::false_type {};
        /** Returns true if the passed type is a shared pointer */
        template <template <typename...> typename Container, typename... Args>
        struct IsC<Container, Container<Args...>> : std::true_type {};
    } // namespace Private

    /** Return true if T is an X */
    template <template <typename...> typename X, typename T>
    UTIL_ICCBOOL container { Private::IsC<X, T>::value };

    // Common uses

    /** Return true if T is a shared_ptr */
    template <typename T> UTIL_ICCBOOL shared_ptr { container<std::shared_ptr, T> };

} // namespace Util::Type::Is
#endif
