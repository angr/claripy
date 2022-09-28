/**
 * @file
 * @brief This file defines a method to create Exprs with standard unary ops
 */
#ifndef R_SRC_CREATE_PRIVATE_UNARY_HPP_
#define R_SRC_CREATE_PRIVATE_UNARY_HPP_

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with a unary op
     *  Expr pointers may not be nullptr
     */
    template <typename Out, typename OpT, typename... Allowed>
    inline Expr::BasePtr unary_explicit(const Expr::BasePtr &x, Expr::OpPyDict &&d) {
        static const Expr::TypeNames<Allowed...> allowed;

        // Static checks
        static_assert(Util::Type::Is::ancestor<Expr::Base, Out>,
                      "Create::Private::unary requires Out be an Expr");
        static_assert(Op::is_unary<OpT>, "Create::Private::unary requires OpT to be unary");

        // Dynamic checks
        UTIL_ASSERT(Error::Expr::Usage, x, "x cannot be nullptr");
        const bool type_ok { CUID::is_any_t<const Expr::Base, Allowed...>(x) };
        UTIL_ASSERT(Error::Expr::Type, type_ok,
                    "operand of invalid type; allowed types: ", allowed);

        // Construct expr
        using Simplify::simplify;
        if constexpr (std::is_same_v<Expr::Bool, Out>) {
            return simplify(Expr::factory<Out>(x->symbolic, Op::factory<OpT>(x), std::move(d)));
        }
        else {
            return simplify(Expr::factory<Out>(x->symbolic, Op::factory<OpT>(x), std::move(d),
                                               Expr::bit_length(x)));
        }
    }

    /** Create a Expr with a unary op
     *  Output type is assumed from input type
     *  x may not be nullptr
     */
    template <typename OpT, typename... Allowed>
    inline Expr::BasePtr unary(const Expr::BasePtr &x, Expr::OpPyDict &&d) {
        static_assert(Op::is_unary<OpT>, "Create::Private::unary requires OpT to be unary");

        // For speed
        if constexpr (sizeof...(Allowed) == 1) {
            return unary_explicit<Allowed..., OpT, Allowed...>(x, std::move(d));
        }

        // Dynamic checks
        UTIL_ASSERT(Error::Expr::Usage, x, "x cannot be nullptr");
        const bool type_ok { CUID::is_any_t<const Expr::Base, Allowed...>(x) };
        UTIL_ASSERT(Error::Expr::Type, type_ok, "operand of wrong type");

        // Construct expr
        using Simplify::simplify;
        if constexpr (Util::Type::Is::in<Expr::Bool, Allowed...>) {
            if (CUID::is_t<Expr::Bool>(x)) {
                return simplify(
                    Expr::factory<Expr::Bool>(x->symbolic, Op::factory<OpT>(x), std::move(d)));
            }
        }
        return simplify(Expr::factory_cuid(x->cuid, x->symbolic, Op::factory<OpT>(x), std::move(d),
                                           Expr::bit_length(x)));
    }

} // namespace Create::Private

#endif
