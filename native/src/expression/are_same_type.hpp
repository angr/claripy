/**
 * @file
 * @brief This file defines equality comparison methods for expressions
 */
#ifndef R_EXPRESSION_ARESAMETYPE_HPP_
#define R_EXPRESSION_ARESAMETYPE_HPP_

#include "bits.hpp"

#include "../error.hpp"

namespace Expression {

    /** Return true if x and y are the same expression type
     *  If ConsiderSize is true, sizes are compared if the types are sized
     *  x and y may not be null pointers
     */
    template <bool ConsiderSize> bool are_same_type(const BasePtr &x, const BasePtr &y) {
        UTILS_AFFIRM_NOT_NULL_DEBUG(x);
        UTILS_AFFIRM_NOT_NULL_DEBUG(y);
        // Type check
        if (x->cuid != y->cuid) {
            Utils::Log::warning(WHOAMI_WITH_SOURCE "failed due to cuid difference");
            return false;
        }
        // Size check, skip if unsized
        if constexpr (ConsiderSize) {
            if (dynamic_cast<CTSC<Expression::Bits>>(x.get()) != nullptr) {
                if (Expression::get_bit_length(x) != Expression::get_bit_length(y)) {
                    Utils::Log::warning(WHOAMI_WITH_SOURCE "failed due to size difference: ",
                                        Expression::get_bit_length(x), " vs ",
                                        Expression::get_bit_length(y));
                    return false;
                }
            }
        }
        return true;
    }

} // namespace Expression

#endif
