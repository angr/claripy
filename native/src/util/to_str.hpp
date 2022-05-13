/**
 * @file
 * \ingroup util
 * @brief This file defines Util::to_str
 */
#ifndef R_SRC_UTIL_TOSTR_HPP_
#define R_SRC_UTIL_TOSTR_HPP_

#include "type.hpp"

#include <sstream>


namespace Util {

    /** This function takes in a set of arguments, and returns a stream that comprises them
     *  Arguments are taken in by constant reference
     *  Strong enums are statically cast to their underlying types if their << operator is
     *  undefined Every other argument must have the << stream operator defined
     *  Note: While marked inline, this is often not inlined by the compiler when it is unlikely
     *  to be called, would cause massive stack growth, etc (the compiler is smarter than us here)
     *  Will print bools as words rather than numbers
     */
    template <typename T, typename... Args> inline T to_stream(Args &&...args) {
        static_assert(Type::Is::ancestor<std::ostream, T>, "T must be an ostream");
        T s;
        if constexpr (Type::Is::in_ignore_const<bool, Args...>) {
            s << std::boolalpha;
        }
        ((s << std::forward<Args>(args)), ...);
        return s; // Copy elision or std::move (no copy ctor exists)
    }

    /** A thin wrapper around to_stream which returns an std::string instead */
    template <typename... Args> inline std::string to_str(Args &&...args) {
        return to_stream<std::ostringstream>(std::forward<Args>(args)...).str();
    }

    /** A thin wrapper around to_str which returns a dynamically allocated char * instead */
    template <typename... Args> inline const char *to_c_str(Args &&...args) {
        std::string r { to_str(std::forward<Args>(args)...) };
        char *const ret { new char[r.size() + 1] };
        std::memcpy(ret, r.data(), r.size());
        ret[r.size()] = 0;
        return ret;
    }

} // namespace Util

#endif
