/**
 * @file
 * @brief This file defines a method to create Exprs with standard unary ops
 */
#ifndef R_CREATE_PRIVATE_UNARY_HPP_
#define R_CREATE_PRIVATE_UNARY_HPP_

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with a unary op
     *  Expr pointers may not be nullptr
     */
    template <typename Out, typename In, typename OpT, typename... Allowed>
    inline Expr::BasePtr unary(const Expr::BasePtr &x, Annotation::SPAV &&sp) {
        namespace Ex = Expr;
        using namespace Simplification;
        namespace Err = Error::Expr;

        // Static checks
        static_assert(Util::is_ancestor<Ex::Base, Out>,
                      "Create::Private::unary requires Out be an Expr");
        static_assert(Util::is_ancestor<Ex::Base, In>,
                      "Create::Private::unary requires In be an Expr");
        static_assert(Op::is_unary<OpT>, "Create::Private::unary requires OpT to be unary");
        if constexpr (Util::is_ancestor<Ex::Bits, Out>) {
            const constexpr bool sized_in { Util::is_ancestor<Ex::Bits, In> };
            static_assert(Util::TD::boolean<sized_in, In>,
                          "Create::Private::unary does not support sized output types without "
                          "sized input types");
        }
        static_assert(Util::qualified_is_in<In, Allowed...>,
                      "Create::Private::unary argument types must be in Allowed");

        // Dynamic checks
        Util::affirm<Err::Usage>(x != nullptr, WHOAMI "x cannot be nullptr");
        Util::affirm<Err::Type>(CUID::is_t<In>(x), WHOAMI "operand must be of type In");

        // Construct expr
        if constexpr (Util::is_ancestor<Ex::Bits, Out>) {
            return simplify(Ex::factory<Out>(x->symbolic, Op::factory<OpT>(x),
                                             Ex::get_bit_length(x), std::move(sp)));
        }
        else {
            return simplify(Ex::factory<Out>(x->symbolic, Op::factory<OpT>(x), std::move(sp)));
        }
    }

} // namespace Create::Private

#endif
