/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::to_str and related functions
 */
#ifndef __UTILS_TOSTR_HPP__
#define __UTILS_TOSTR_HPP__

#include "apply.hpp"
#include "private/ostream.hpp"

#include <sstream>


namespace Utils {

    /** This function takes in a set of arguments, and << applies them to s
     *  Arguments are taken in by constant reference
     *  Strong enums are statically cast to their underlying types if their << operator is
     * undefined Every other argument must have the << stream operator defined
     */
    template <typename... Args>
    void apply_to_ostringstream(std::ostringstream &s, const Args &...args) {
        apply<Private::OStreamConst>(s, args...);
    }

    /** This function takes in a set of arguments, and returns a string that comprises them
     *  Arguments are taken in by constant reference
     *  Strong enums are statically cast to their underlying types if their << operator is
     * undefined Every other argument must have the << stream operator defined
     */
    template <typename... Args> std::string to_str(const Args &...args) {
        std::ostringstream s;
        apply_to_ostringstream(s, args...);
        return s.str();
    }

} // namespace Utils

#endif
