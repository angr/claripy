/**
 * @file
 * \ingroup util
 * @brief This file defines a way to get the index of a type template arguments
 */
#ifndef R_SRC_UTIL_TYPE_VARIANTINDEX_HPP_
#define R_SRC_UTIL_TYPE_VARIANTINDEX_HPP_

#include "list.hpp"
#include "remove_cvr.hpp"

#include <variant>

namespace Util::Type {
    namespace Private {
        /** Returns List<Args...> given std::variant<Args...> */
        template <typename... Args> constexpr List<Args...> from_var(std::variant<Args...> &&) {
            return std::declval<List<Args...>>();
        }
        /** Return the index of T in V's template arguments and run a static check */
        template <typename V, typename T> constexpr unsigned index() {
            using TL = decltype(Private::from_var(std::declval<RemoveCVR<V>>()));
            const unsigned ret { TL::template find<T, true> };
            using SanityCheck = decltype(std::get<ret>(std::declval<V>()));
            static_assert(Util::Type::Is::same_ignore_cvr<SanityCheck, T>, "Sanity check failed");
            return ret;
        }
    } // namespace Private

    /** Return the index of T in V's template arguments */
    template <typename V, typename T>
    static inline const constexpr unsigned index { Private::index<V, T>() };
} // namespace Util::Type

#endif
