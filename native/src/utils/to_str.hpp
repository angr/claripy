/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::to_str
 */
#ifndef R_UTILS_TOSTR_HPP_
#define R_UTILS_TOSTR_HPP_

#include "ostream.hpp"

#include <sstream>


namespace Utils {

    /** This function takes in a set of arguments, and returns a string that comprises them
     *  Arguments are taken in by constant reference
     *  Strong enums are statically cast to their underlying types if their << operator is
     *  undefined Every other argument must have the << stream operator defined
     *  Note: While marked inline, this is often not inlined by the compiler when it is unlikely
     *  to be called, would cause massive stack growth, etc (the compiler is smarter than us here)
     */
    template <typename... Args> inline std::string to_str(const Args &...args) {
        std::ostringstream s;
        (OStream(s, args), ...);
        return s.str();
    }

} // namespace Utils

#endif
