/**
 * @file
 * \ingroup util
 * @brief This file defines a type which wraps another type
 */
#ifndef R_UTIL_TYPETOTYPE_HPP_
#define R_UTIL_TYPETOTYPE_HPP_


namespace Util {

    /** This type wraps another type */
    template <typename T> struct TypeToType { using Type = T; };

} // namespace Util

#endif
