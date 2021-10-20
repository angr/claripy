/**
 * @file
 * \ingroup util
 * @brief Defines is_shared_ptr
 */
#ifndef R_UTIL_ISSHAREDPTR_HPP_
#define R_UTIL_ISSHAREDPTR_HPP_

#include <memory>
#include <type_traits>


namespace Util {

    namespace Private {
        /** Returns true if T is a shared pointer */
        template <typename> struct IsSharedPtr : std::false_type {};
        /** Returns true if the passed type is a shared pointer */
        template <typename... Args>
        struct IsSharedPtr<std::shared_ptr<Args...>> : std::true_type {};
    } // namespace Private

    /** Return true if T is a shared_ptr */
    template <typename T> UTILS_ICCBOOL is_shared_ptr { Private::IsSharedPtr<T>::value };

} // namespace Util
#endif
