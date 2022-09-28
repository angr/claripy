/**
 * @file
 * @brief This file defines equality comparison methods for exprs
 */
#ifndef R_SRC_EXPR_ARESAMETYPE_HPP_
#define R_SRC_EXPR_ARESAMETYPE_HPP_

#include "bits.hpp"

#include "../error.hpp"

namespace Expr {

    /** Return true if x and y are the same expr type
     *  If ConsiderSize is true, sizes are compared if the types are sized
     *  x and y may not be null pointers
     *  Logs warnings if are_same_type returns will false
     */
    template <bool ConsiderSize> bool are_same_type(const BasePtr &x, const BasePtr &y) {
        UTIL_ASSERT_NOT_NULL_DEBUG(x);
        UTIL_ASSERT_NOT_NULL_DEBUG(y);
        // Type check
        if (x->cuid != y->cuid) {
            Util::Log::warning(WHOAMI "failed due to cuid difference");
            return false;
        }
        // Size check, skip if unsized
        if constexpr (ConsiderSize) {
            if (dynamic_cast<CTSC<Expr::Bits>>(x.get())) {
                if (Expr::bit_length(x) != Expr::bit_length(y)) {
                    Util::Log::warning(WHOAMI "failed due to size difference: ",
                                       Expr::bit_length(x), " vs ", Expr::bit_length(y));
                    return false;
                }
            }
        }
        return true;
    }

} // namespace Expr

#endif
