/**
 * @file
 * @brief This file defines a method to create Exprs with standard ternary ops
 */
#ifndef R_CREATE_PRIVATE_TERNARY_HPP_
#define R_CREATE_PRIVATE_TERNARY_HPP_

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with a ternary op
     *  Expr pointers may not be nullptr
     */
    template <typename Out, typename OpT, typename... Allowed>
    inline Expr::BasePtr ternary_explicit(const Expr::BasePtr &first, const Expr::BasePtr &second,
                                          const Expr::BasePtr &third, Annotation::SPAV &&sp) {
        static const Expr::TypeNames<Allowed...> allowed;
        using namespace Simplification;
        namespace Err = Error::Expr;

        // Static checks
        static_assert(Util::Type::Is::ancestor<Expr::Base, Out>,
                      "Create::Private::ternary requires Out be an Expr");
        static_assert(Op::is_ternary<OpT>, "Create::Private::ternary requires a ternary OpT");

        // Dynamic checks
        Util::affirm<Err::Usage>(first != nullptr, second != nullptr && third != nullptr,
                                 WHOAMI "Expr pointer arguments may not be nullptr");
        Util::affirm<Err::Type>(CUID::is_any_t<const Expr::Base, Allowed...>(first),
                                WHOAMI "first operand of invalid type; allowed types: ", allowed);

        // Construct expr (static casts are safe because of previous checks)
        const bool sym { first->symbolic || second->symbolic || third->symbolic };
        if constexpr (std::is_same_v<Expr::Bool, Out>) {
            return simplify(
                Expr::factory<Out>(sym, Op::factory<OpT>(first, second, third), std::move(sp)));
        }
        else {
            using E = Util::Err::Type;
            Util::affirm<E>(first->cuid == second->cuid, WHOAMI "second operand of wrong type");
            Util::affirm<E>(first->cuid == third->cuid, WHOAMI "third operand of wrong type");
            return simplify(Expr::factory<Out>(sym, Op::factory<OpT>(first, second, third),
                                               Expr::get_bit_length(first) +
                                                   Expr::get_bit_length(second) +
                                                   Expr::get_bit_length(third),
                                               std::move(sp)));
        }
    }

} // namespace Create::Private

#endif
