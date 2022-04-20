/**
 * @file
 * \ingroup util
 * @brief This file defines type pair type
 */
#ifndef R_SRC_UTIL_TYPE_PAIR_HPP_
#define R_SRC_UTIL_TYPE_PAIR_HPP_

namespace Util::Type {

    /** A type which is a pair of two other types */
    template <typename A, typename B> struct Pair {
        /** The first type */
        using First = A;
        /** The second type */
        using Second = B;
    };

} // namespace Util::Type

#endif
