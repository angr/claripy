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
    inline Expr::BasePtr unary_explicit(const Expr::BasePtr &x, Annotation::SPAV &&sp) {
        static const Expr::TypeNames<Allowed...> allowed;
        using namespace Simplify;
        namespace Err = Error::Expr;

        // Static checks
        static_assert(Util::Type::Is::ancestor<Expr::Base, Out>,
                      "Create::Private::unary requires Out be an Expr");
        static_assert(Op::is_unary<OpT>, "Create::Private::unary requires OpT to be unary");

        // Dynamic checks
        UTIL_ASSERT(Err::Usage, x != nullptr, "x cannot be nullptr");
        const bool type_ok { CUID::is_any_t<const Expr::Base, Allowed...>(x) };
        UTIL_ASSERT(Err::Type, type_ok, "operand of invalid type; allowed types: ", allowed);

        // Construct expr
        if constexpr (std::is_same_v<Expr::Bool, Out>) {
            return simplify(Expr::factory<Out>(x->symbolic, Op::factory<OpT>(x), std::move(sp)));
        }
        else {
            return simplify(Expr::factory<Out>(x->symbolic, Op::factory<OpT>(x),
                                               Expr::get_bit_length(x), std::move(sp)));
        }
    }

    /** Create a Expr with a unary op
     *  Output type is assumed from input type
     *  x may not be nullptr
     */
    template <typename OpT, typename... Allowed>
    inline Expr::BasePtr unary(const Expr::BasePtr &x, Annotation::SPAV &&sp) {
        static_assert(Op::is_unary<OpT>, "Create::Private::unary requires OpT to be unary");
        using namespace Simplify;
        namespace Err = Error::Expr;

        // For speed
        if constexpr (sizeof...(Allowed) == 1) {
            return unary_explicit<Allowed..., OpT, Allowed...>(x, std::move(sp));
        }

        // Dynamic checks
        UTIL_ASSERT(Err::Usage, x != nullptr, "x cannot be nullptr");
        const bool type_ok { CUID::is_any_t<const Expr::Base, Allowed...>(x) };
        UTIL_ASSERT(Err::Type, type_ok, "operand of wrong type");

        // Construct expr
        if constexpr (Util::Type::Is::in<Expr::Bool, Allowed...>) {
            if (CUID::is_t<Expr::Bool>(x)) {
                return simplify(
                    Expr::factory<Expr::Bool>(x->symbolic, Op::factory<OpT>(x), std::move(sp)));
            }
        }
        return simplify(Expr::factory_cuid(x->cuid, x->symbolic, Op::factory<OpT>(x),
                                           Expr::get_bit_length(x), std::move(sp)));
    }

} // namespace Create::Private

#endif
