/**
 * @file
 * \ingroup utils
 * @brief This file defines a methods like std::is_same but that can unqualify their inputs
 */
#ifndef R_UTILS_ISSAME_HPP_
#define R_UTILS_ISSAME_HPP_

#include "macros.hpp"

#include <type_traits>


namespace Utils {

    /** std::is_same_v */
    template <typename T, typename U> UTILS_ICCBOOL is_exactly_same { std::is_same_v<T, U> };

    /** Verifies that Wrap<T> == Wrap<U> */
    template <typename T, typename U, template <typename> typename Wrap>
    UTILS_ICCBOOL is_wrap_same { is_exactly_same<Wrap<T>, Wrap<U>> };

    /** Verifies that the const unqualified types are the same */
    template <typename T, typename U>
    UTILS_ICCBOOL is_same_ignore_const { is_wrap_same<T, U, std::remove_const_t> };

    /** Verifies that the cv unqualified types are the same */
    template <typename T, typename U>
    UTILS_ICCBOOL is_same_ignore_cv { is_wrap_same<T, U, std::remove_cv_t> };

} // namespace Utils

#endif
