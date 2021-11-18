/**
 * @file
 * @brief This file defines a method to create Exprs with standard flat ops
 */
#ifndef R_CREATE_PRIVATE_FLAT_HPP_
#define R_CREATE_PRIVATE_FLAT_HPP_

#include "../constants.hpp"


namespace Create::Private {

    /** Ors the sym value of each Expr::BasePtr item in C */
    template <typename C> inline bool flat_sym(C &&o) {
        bool sym { false };
        for (const Expr::BasePtr &i : o) {
#ifdef DEBUG
            Util::affirm<Error::Expr::Usage>(i != nullptr, WHOAMI "Null operand detected");
#endif
            sym |= i->symbolic;
        }
        return sym;
    }

    /** Create a Expr with a flat op
     *  operands' pointers may not be nullptr
     */
    template <typename Out, typename OpT, typename... Allowed>
    inline Expr::BasePtr flat_explicit(Op::FlatArgs &&operands, Annotation::SPAV &&sp) {
        using namespace Simplification;
        namespace Err = Error::Expr;

        // Checks
        static_assert(Op::is_flat<OpT>, "Create::Private::flat requires OpT to be flat");
        static_assert(Util::Type::is_in<Out, Allowed...>,
                      "Create::Private::flat argument types must be in Allowed");
        Util::affirm<Err::Size>(operands.size() >= 2, WHOAMI "operands are empty.");
        UTIL_AFFIRM_NOT_NULL_DEBUG(operands[0]);
        Util::affirm<Err::Type>(CUID::is_t<Out>(operands[0]),
                                WHOAMI "operands[0] is the wrong type");

        const bool sym { flat_sym(operands) };
        if constexpr (std::is_same_v<Expr::Bool, Out>) {
            return simplify(
                Expr::factory<Out>(sym, Op::factory<OpT>(std::move(operands)), std::move(sp)));
        }
        else {
            const UInt len { Expr::get_bit_length(operands[0]) }; // Before move
            return simplify(
                Expr::factory<Out>(sym, Op::factory<OpT>(std::move(operands)), len, std::move(sp)));
        }
    }

    /** Create a Expr with a flat op
     *  Out type is the same as operands[0]
     *  Expr pointers may not be nullptr
     */
    template <typename OpT, typename... Allowed>
    inline Expr::BasePtr flat(Op::FlatArgs &&operands, Annotation::SPAV &&sp) {
        using namespace Simplification;
        namespace Err = Error::Expr;

        // For speed
        if constexpr (sizeof...(Allowed) == 1) {
            return flat_explicit<Allowed..., OpT, Allowed...>(std::move(operands), std::move(sp));
        }

        // Checks
        static_assert(Op::is_flat<OpT>, "Create::Private::flat requires OpT to be flat");
        Util::affirm<Err::Size>(operands.size() >= 2, WHOAMI "operands are empty.");
        UTIL_AFFIRM_NOT_NULL_DEBUG(operands[0]);
        Util::affirm<Err::Type>(CUID::is_any_t<const Expr::Base, Allowed...>(operands[0]),
                                WHOAMI "operands[0] is the wrong type");

        // Create Expr
        const bool sym { flat_sym(operands) };
        if constexpr (Util::Type::is_in<Expr::Bool, Allowed...>) {
            if (CUID::is_t<Expr::Bool>(operands[0])) {
                return simplify(Expr::factory<Expr::Bool>(
                    sym, Op::factory<OpT>(std::move(operands)), std::move(sp)));
            }
        }
        const UInt len { Expr::get_bit_length(operands[0]) }; // Before move
        return simplify(Expr::factory_cuid(
            operands[0]->cuid, sym, Op::factory<OpT>(std::move(operands)), len, std::move(sp)));
    }

} // namespace Create::Private

#endif
