/**
 * @file
 * \ingroup util
 * @brief This file define remove_cvr
 */
#ifndef R_SRC_UTIL_TYPE_REMOVECVR_HPP_
#define R_SRC_UTIL_TYPE_REMOVECVR_HPP_

#include <type_traits>


namespace Util::Type {

    /** Remove cv and reference */
    template <typename T> using RemoveCVR = std::remove_cv_t<std::remove_reference_t<T>>;

} // namespace Util::Type

#endif
