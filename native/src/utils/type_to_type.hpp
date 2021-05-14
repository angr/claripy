/**
 * @file
 * \ingroup utils
 * @brief This file defines a type which wraps another type
 */
#ifndef R_UTILS_TYPETOTYPE_HPP_
#define R_UTILS_TYPETOTYPE_HPP_


namespace Utils {

    /** This type wraps another type */
    template <typename T> struct TypeToType { using Type = T; };

} // namespace Utils

#endif
