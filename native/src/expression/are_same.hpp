/**
 * @file
 * @brief This file defines equality comparison methods for expressions
 */
#ifndef __EXPRESSION_ARESAME_HPP__
#define __EXPRESSION_ARESAME_HPP__

#include "bits.hpp"

#include "../error.hpp"


namespace Expression {

    /** Return true if x is a T */
    template <typename T> bool is_t(const BasePtr &x) { return x->cuid == T::static_cuid; }

    /** Return true if x and y are the same expression type
     *  If ConsiderSize is true, sizes are compared if the types are sized
     */
    template <bool ConsiderSize> bool are_same(const BasePtr &x, const BasePtr &y) {
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
                return xcast->size == dynamic_cast<CTSC<Bits>>(y.get())->size;
            }
        }
        return true;
    }


} // namespace Expression

#endif
