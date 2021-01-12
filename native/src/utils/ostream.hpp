/**
 * @file
 * \ingroup utils
 * @brief This file defines an ostream operator wrapper that can be passed to Utils::apply
 * Additionally, this function statically casts strong enums to their underlying types
 */
#ifndef __UTILS_OSTREAM_HPP__
#define __UTILS_OSTREAM_HPP__

#include "private/ostream_helper_conversions.hpp"

#include "../macros.hpp"


namespace Utils {

    /** An ostream wrapper that augments << by default defining it for strong enums
     *  If the strong enum already has a << operator defined, this is a passthrough
     */
    template <typename T, typename U> inline void OStream(T &left, const U &right) {
        left << Private::ostream_helper_conversions(right);
    }

} // namespace Utils

#endif
