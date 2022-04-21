/**
 * @file
 * \ingroup util
 * @brief This file defines an ostream operator wrapper that can be passed to Util::apply
 * Additionally, this function statically casts strong enums to their underlying types
 */
#ifndef R_SRC_UTIL_OSTREAM_HPP_
#define R_SRC_UTIL_OSTREAM_HPP_

#include "to_underlying.hpp"
#include "type.hpp"


namespace Util {

    /** An ostream wrapper that augments << by default defining it for strong enums
     *  If the strong enum already has a << operator defined, this is a passthrough
     */
    template <typename T, typename U> inline void OStream(T &left, const U &right) {
        if constexpr (Type::Is::strong_enum<U> && not Type::Has::ostream_op<U>) {
            left << to_underlying(right);
        }
        else {
            left << right;
        }
    }

} // namespace Util

#endif
