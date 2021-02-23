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
            return false;
        }
        // Size check
        if constexpr (ConsiderSize) {
            using namespace Constants;
            using namespace Expression;
            // If sized
            if (const auto xcast { dynamic_cast<CTSC<Bits>>(x.get()) }; xcast) {
                return xcast->bit_length == dynamic_cast<CTSC<Bits>>(y.get())->bit_length;
            }
        }
        return true;
    }

} // namespace Expression

#endif
