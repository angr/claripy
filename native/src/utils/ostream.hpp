/**
 * @file
 * \ingroup utils
 * @brief This file defines an ostream operator wrapper that can be passed to Utils::apply
 * Additionally, this function statically casts strong enums to their underlying types
 */
#ifndef R_UTILS_OSTREAM_HPP_
#define R_UTILS_OSTREAM_HPP_

#include "is_strong_enum.hpp"
#include "private/has_ostream_op.hpp"
#include "to_underlying.hpp"


namespace Utils {

    /** An ostream wrapper that augments << by default defining it for strong enums
     *  If the strong enum already has a << operator defined, this is a passthrough
     *  Warning, this function will allow type promotion even if the compiler prevents it
     */
    template <typename T, typename U> inline void OStream(T &left, const U &right) {
        if constexpr (is_strong_enum<U> && !Private::has_ostream_op<U>) {
            left << to_underlying(right);
        }
        else {
            using Right = Utils::Function<decltype(left << right)>::Arg<1>;
            left << static_cast<Right>(right); // Prevent implicit type promotion
        }
    }

} // namespace Utils

#endif
