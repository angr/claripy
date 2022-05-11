/**
 * @file
 * \ingroup util
 * @brief This file defines a methods like std::is_same but that can unqualify their inputs
 */
#ifndef R_SRC_UTIL_TYPE_IS_SAME_HPP_
#define R_SRC_UTIL_TYPE_IS_SAME_HPP_

#include "../../macros.hpp"
#include "../remove_cvr.hpp"

#include <type_traits>


namespace Util::Type::Is {

    /** Verifies that Wrap<T> == Wrap<U> */
    template <typename T, typename U, template <typename> typename Wrap>
    UTIL_ICCBOOL wrap_same { std::is_same_v<Wrap<T>, Wrap<U>> };

    /** Verifies that the const unqualified types are the same */
    template <typename T, typename U>
    UTIL_ICCBOOL same_ignore_const { wrap_same<T, U, std::remove_const_t> };

    /** Verifies that the cv unqualified types are the same */
    template <typename T, typename U>
    UTIL_ICCBOOL same_ignore_cv { wrap_same<T, U, std::remove_cv_t> };

    /** Verifies that the cv unqualified types are the same */
    template <typename T, typename U> UTIL_ICCBOOL same_ignore_cvr { wrap_same<T, U, RemoveCVR> };

} // namespace Util::Type::Is

#endif
