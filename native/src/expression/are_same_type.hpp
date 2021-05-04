/**
 * @file
 * @brief This file defines equality comparison methods for expressions
 */
#ifndef __EXPRESSION_ARESAMETYPE_HPP__
#define __EXPRESSION_ARESAMETYPE_HPP__

#include "bits.hpp"

#include "../error.hpp"


namespace Expression {

    /** Return true if x and y are the same expression type
     *  If ConsiderSize is true, sizes are compared if the types are sized
     */
    template <bool ConsiderSize> bool are_same_type(const BasePtr &x, const BasePtr &y) {
        namespace Err = Error::Expression;
        // Type check
        if (x->cuid != y->cuid) {
            Utils::Log::warning(WHOAMI_WITH_SOURCE "failed due to cuid difference");
            return false;
        }
        // Size check
        if constexpr (ConsiderSize) {
            Utils::affirm<Utils::Error::Unexpected::IncorrectUsage>(
                dynamic_cast<Constants::CTSC<Expression::Bits>>(x.get()) != nullptr,
                WHOAMI_WITH_SOURCE, "called on non-bits subclasses");
            if (Expression::get_bit_length(x) != Expression::get_bit_length(y)) {
                Utils::Log::warning(WHOAMI_WITH_SOURCE "failed due to size difference:",
                                    Expression::get_bit_length(x), " vs ",
                                    Expression::get_bit_length(y));
                return false;
            }
        }
        return true;
    }

} // namespace Expression

#endif
