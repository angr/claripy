/**
 * @file
 * @brief This file defines a method to create Expressions with standard unary ops
 */
#ifndef __CREATE_PRIVATE_UNARY_HPP__
#define __CREATE_PRIVATE_UNARY_HPP__

#include "size.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with a unary op */
    template <typename T, typename OpT, typename... Allowed>
    inline EBasePtr unary(EAnVec &&av, const EBasePtr &x) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type checks
        static_assert(Utils::qualified_is_in<T, Allowed...>,
                      "Create::Private::unary argument types must be in Allowed");
        static_assert(Op::is_unary<OpT>, "Create::Private::unary requries OpT to be unary");
        Utils::affirm<Err::Type>(Ex::is_t<T>(x),
                                 "Create::Private::unary operand must be of type T");

        // Construct expression
        if constexpr (Utils::is_ancestor<Ex::Bits, T>) {
            return simplify(Ex::factory<T>(std::forward<EAnVec>(av), x->symbolic,
                                           Op::factory<OpT>(x), size(x)));
        }
        else {
            return simplify(
                Ex::factory<T>(std::forward<EAnVec>(av), x->symbolic, Op::factory<OpT>(x)));
        }
    }

} // namespace Create::Private


#endif
