/**
 * @file
 * \ingroup util
 * @brief Defines is_x and related functions
 */
#ifndef R_UTIL_TYPE_ISX_HPP_
#define R_UTIL_TYPE_ISX_HPP_

#include <memory>
#include <type_traits>


namespace Util::Type {

    namespace Private {
        /** Returns true if T is a shared pointer */
        template <template <typename...> typename, typename> struct IsX : std::false_type {};
        /** Returns true if the passed type is a shared pointer */
        template <template <typename...> typename Container, typename... Args>
        struct IsX<Container, Container<Args...>> : std::true_type {};
    } // namespace Private

    /** Return true if T is an X */
    template <template <typename...> typename X, typename T>
    UTIL_ICCBOOL is_x { Private::IsX<X, T>::value };

    // Common uses

    /** Return true if T is a shared_ptr */
    template <typename T> UTIL_ICCBOOL is_shared_ptr { is_x<std::shared_ptr, T> };

} // namespace Util::Type
#endif
