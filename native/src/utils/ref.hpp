/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::ref
 */
#ifndef R_UTILS_REF_HPP_
#define R_UTILS_REF_HPP_


namespace Utils {

    /** This allows passing compile-time literals by reference */
    template <typename T, T N> inline constexpr const T ref { N };

} // namespace Utils

#endif
