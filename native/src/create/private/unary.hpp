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
    template <typename Out, typename In, typename OpT, typename... Allowed>
    inline EBasePtr unary(EAnVec &&av, const EBasePtr &x) {
        static_assert(Utils::is_ancestor<Expression::Base, Out>,
                      "Create::Private::unary requires Out be an Expression");
        static_assert(Utils::is_ancestor<Expression::Base, In>,
                      "Create::Private::unary requires In be an Expression");
        static_assert(Op::is_unary<OpT>, "Create::Private::unary requries OpT to be unary");
        if constexpr (Utils::is_ancestor<Expression::Bits, Out>) {
            const constexpr bool sized_in { Utils::is_ancestor<Expression::Bits, In> };
            static_assert(Utils::TD::boolean<sized_in, In>,
                          "Create::Private::unary does not suppot sized output types without "
                          "sized input types");
        }

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type checks
        static_assert(Utils::qualified_is_in<In, Allowed...>,
                      "Create::Private::unary argument types must be in Allowed");
        Utils::affirm<Err::Type>(Ex::is_t<In>(x), WHOAMI_WITH_SOURCE "operand must be of type In");

        // Construct expression
        if constexpr (Utils::is_ancestor<Ex::Bits, Out>) {
            return simplify(Ex::factory<Out>(std::forward<EAnVec>(av), x->symbolic,
                                             Op::factory<OpT>(x), size(x)));
        }
        else {
            return simplify(
                Ex::factory<Out>(std::forward<EAnVec>(av), x->symbolic, Op::factory<OpT>(x)));
        }
    }

} // namespace Create::Private

#endif
