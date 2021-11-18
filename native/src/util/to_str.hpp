/**
 * @file
 * \ingroup util
 * @brief This file defines Util::to_str
 */
#ifndef R_UTIL_TOSTR_HPP_
#define R_UTIL_TOSTR_HPP_

#include "ostream.hpp"
#include "type.hpp"

#include <sstream>


namespace Util {

    /** This function takes in a set of arguments, and returns a stream that comprises them
     *  Arguments are taken in by constant reference
     *  Strong enums are statically cast to their underlying types if their << operator is
     *  undefined Every other argument must have the << stream operator defined
     *  Note: While marked inline, this is often not inlined by the compiler when it is unlikely
     *  to be called, would cause massive stack growth, etc (the compiler is smarter than us here)
     */
    template <typename T, typename... Args> inline T to_stream(Args &&...args) {
        static_assert(Type::is_ancestor<std::ostream, T>, "T must be an ostream");
        T s;
        (OStream(s, std::forward<Args>(args)), ...);
        return s; // Copy elision or std::move (no copy ctor exists)
    }

    /** This function takes in a set of arguments, and returns a string that comprises them
     *  Arguments are taken in by constant reference
     *  Strong enums are statically cast to their underlying types if their << operator is
     *  undefined Every other argument must have the << stream operator defined
     *  Note: While marked inline, this is often not inlined by the compiler when it is unlikely
     *  to be called, would cause massive stack growth, etc (the compiler is smarter than us here)
     */
    template <typename... Args> inline std::string to_str(Args &&...args) {
        return to_stream<std::ostringstream>(std::forward<Args>(args)...).str();
    }

} // namespace Util

#endif
