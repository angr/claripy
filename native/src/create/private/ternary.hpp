/**
 * @file
 * @brief This file defines a method to create Exprs with standard ternary ops
 */
#ifndef R_SRC_CREATE_PRIVATE_TERNARY_HPP_
#define R_SRC_CREATE_PRIVATE_TERNARY_HPP_

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with a ternary op
     *  Expr pointers may not be nullptr
     */
    template <typename Out, typename OpT, typename... Allowed>
    inline Expr::BasePtr ternary_explicit(const Expr::BasePtr &first, const Expr::BasePtr &second,
                                          const Expr::BasePtr &third, Expr::OpPyDict &&d) {
        static const Expr::TypeNames<Allowed...> allowed;

        // Static checks
        static_assert(Util::Type::Is::ancestor<Expr::Base, Out>,
                      "Create::Private::ternary requires Out be an Expr");
        static_assert(Op::is_ternary<OpT>, "Create::Private::ternary requires a ternary OpT");

        // Dynamic checks
        UTIL_ASSERT(Error::Expr::Usage, first, second && third,
                    "Expr pointer arguments may not be nullptr");
        const bool type_ok { CUID::is_any_t<const Expr::Base, Allowed...>(first) };
        UTIL_ASSERT(Error::Expr::Type, type_ok,
                    "first operand of invalid type; allowed types: ", allowed);

        // Construct expr (static casts are safe because of previous checks)
        using Simplify::simplify;
        const bool sym { first->symbolic || second->symbolic || third->symbolic };
        if constexpr (std::is_same_v<Expr::Bool, Out>) {
            return simplify(
                Expr::factory<Out>(sym, Op::factory<OpT>(first, second, third), std::move(d)));
        }
        else {
            using E = Util::Err::Type;
            UTIL_ASSERT(E, first->cuid == second->cuid, "second operand of wrong type");
            UTIL_ASSERT(E, first->cuid == third->cuid, "third operand of wrong type");
            return simplify(Expr::factory<Out>(
                sym, Op::factory<OpT>(first, second, third), std::move(d),
                Expr::bit_length(first) + Expr::bit_length(second) + Expr::bit_length(third)));
        }
    }

} // namespace Create::Private

#endif
