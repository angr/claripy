/**
 * @file
 * \ingroup utils
 * @brief This file defines a methods like std::is_same but that can unqualify their inpus
 */
#ifndef __UTILS_ISSAME_HPP__
#define __UTILS_ISSAME_HPP__

#include <type_traits>


namespace Utils {

    /** std::is_same_v */
    template <typename T, typename U>
    const inline constexpr bool is_exactly_same { std::is_same_v<T, U> };

    /** Verifies that Wrap<T> == Wrap<U> */
    template <typename T, typename U, template <typename> typename Wrap>
    const inline constexpr bool is_wrap_same { is_exactly_same<Wrap<T>, Wrap<U>> };

    /** Verifies that the const unqualified types are the same */
    template <typename T, typename U>
    const inline constexpr bool is_same_ignore_const { is_wrap_same<T, U, std::remove_const_t> };

    /** Verifies that the cv unqualified types are the same */
    template <typename T, typename U>
    const inline constexpr bool is_same_ignore_cv { is_wrap_same<T, U, std::remove_cv_t> };

} // namespace Utils

#endif
