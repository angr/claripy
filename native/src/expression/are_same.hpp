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
    template <typename T, bool AllowKin> constexpr bool is_t(const BasePtr &x) {
        static_assert(Utils::is_ancestor<Base, T>, "T must subclass Base");
        if constexpr (std::is_final_v<T>) {
            return x->cuid == T::static_cuid;
        }
        else if constexpr (AllowKin) {
            if constexpr (Utils::is_same_ignore_cv<T, Base>) {
                return true;
            }
            else {
                return dynamic_cast<Constants::CTSC<T>>(x.get()) != nullptr;
            }
        }
        else {
            return false;
        }
    }

    /** Return true if x is a T */
    template <typename T> bool is_t(const BasePtr &x) {
        static_assert(std::is_final_v<T>,
                      "is_t only allowed without AllowKin defined if T is final");
        return is_t<T, false>(x);
    }

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
