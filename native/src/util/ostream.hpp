/**
 * @file
 * \ingroup util
 * @brief This file defines an ostream operator wrapper that can be passed to Util::apply
 * Additionally, this function statically casts strong enums to their underlying types
 */
#ifndef R_UTIL_OSTREAM_HPP_
#define R_UTIL_OSTREAM_HPP_

#include "is_strong_enum.hpp"
#include "private/has_ostream_op.hpp"
#include "to_underlying.hpp"


namespace Util {

    /** An ostream wrapper that augments << by default defining it for strong enums
     *  If the strong enum already has a << operator defined, this is a passthrough
     */
    template <typename T, typename U> inline void OStream(T &left, const U &right) {
        if constexpr (is_strong_enum<U> && !Private::has_ostream_op<U>) {
            left << to_underlying(right);
        }
        else {
            left << right;
        }
    }

} // namespace Util

#endif
