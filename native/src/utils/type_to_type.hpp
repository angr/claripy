/**
 * @file
 * \ingroup utils
 * @brief This file defines a type which wraps another type
 */
#ifndef __UTILS_TYPETOTYPE_HPP__
#define __UTILS_TYPETOTYPE_HPP__


namespace Utils {

    /** This type wraps another type */
    template <typename T> struct TypeToType { using Type = T; };

} // namespace Utils

#endif
