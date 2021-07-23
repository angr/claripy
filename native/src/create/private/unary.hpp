/**
 * @file
 * @brief This file defines a method to create Expressions with standard unary ops
 */
#ifndef R_CREATE_PRIVATE_UNARY_HPP_
#define R_CREATE_PRIVATE_UNARY_HPP_

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with a unary op
     *  Expression pointers may not be nullptr
     */
    template <typename Out, typename In, typename OpT, typename... Allowed>
    inline EBasePtr unary(const EBasePtr &x, SPAV &&sp) {
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Static checks
        static_assert(Utils::is_ancestor<Ex::Base, Out>,
                      "Create::Private::unary requires Out be an Expression");
        static_assert(Utils::is_ancestor<Ex::Base, In>,
                      "Create::Private::unary requires In be an Expression");
        static_assert(Op::is_unary<OpT>, "Create::Private::unary requires OpT to be unary");
        if constexpr (Utils::is_ancestor<Ex::Bits, Out>) {
            const constexpr bool sized_in { Utils::is_ancestor<Ex::Bits, In> };
            static_assert(Utils::TD::boolean<sized_in, In>,
                          "Create::Private::unary does not support sized output types without "
                          "sized input types");
        }
        static_assert(Utils::qualified_is_in<In, Allowed...>,
                      "Create::Private::unary argument types must be in Allowed");

        // Dynamic checks
        Utils::affirm<Err::Usage>(x != nullptr, WHOAMI_WITH_SOURCE "x cannot be nullptr");
        Utils::affirm<Err::Type>(CUID::is_t<In>(x),
                                 WHOAMI_WITH_SOURCE "operand must be of type In");

        // Construct expression
        if constexpr (Utils::is_ancestor<Ex::Bits, Out>) {
            return simplify(Ex::factory<Out>(x->symbolic, Op::factory<OpT>(x),
                                             Ex::get_bit_length(x), std::move(sp)));
        }
        else {
            return simplify(Ex::factory<Out>(x->symbolic, Op::factory<OpT>(x), std::move(sp)));
        }
    }

} // namespace Create::Private

#endif
