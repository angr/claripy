/**
 * @file
 * \ingroup util
 * @brief This file defines a type which wraps another type
 */
#ifndef R_SRC_UTIL_TYPE_TOTYPE_HPP_
#define R_SRC_UTIL_TYPE_TOTYPE_HPP_


namespace Util::Type {

    /** This type wraps another type */
    template <typename T> struct ToType { using Type = T; };

} // namespace Util::Type

#endif
