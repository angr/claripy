/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::ref
 */
#ifndef __UTILS_REF_HPP__
#define __UTILS_REF_HPP__


namespace Utils {

    /** This allows passing compile-time literals by reference */
    template <typename T, T N> static constexpr const T ref { N };

} // namespace Utils

#endif
