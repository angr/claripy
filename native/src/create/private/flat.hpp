/**
 * @file
 * @brief This file defines a method to create Exprs with standard flat ops
 */
#ifndef R_CREATE_PRIVATE_FLAT_HPP_
#define R_CREATE_PRIVATE_FLAT_HPP_

#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with a flat op
     *  operands' pointers may not be nullptr
     */
    template <typename T, typename OpT, SizeMode Mode, typename... Allowed>
    inline Expr::BasePtr flat(typename OpT::OpContainer &&operands, Annotation::SPAV &&sp) {
        namespace Ex = Expr;
        using namespace Simplification;
        namespace Err = Error::Expr;

        // Checks
        static_assert(Op::is_flat<OpT>, "Create::Private::flat requires OpT to be flat");
        static_assert(Util::qualified_is_in<T, Allowed...>,
                      "Create::Private::flat argument types must be in Allowed");
#ifdef DEBUG
        for (const auto &i : operands) {
            Util::affirm<Err::Usage>(i != nullptr,
                                     WHOAMI_WITH_SOURCE "operands' pointers cannot be nullptrs");
        }
#endif
        Util::affirm<Err::Size>(operands.size() >= 2, WHOAMI_WITH_SOURCE "operands are empty.");
        Util::affirm<Err::Type>(CUID::is_t<T>(operands[0]),
                                WHOAMI_WITH_SOURCE "operands[0] is the wrong type");

        // Calculate simple sym
        bool sym { false };
        for (const auto &i : operands) {
            sym |= i->symbolic;
        }

        // Construct expr (static casts are safe because of previous checks)
        if constexpr (Util::is_ancestor<Ex::Bits, T>) {
            static_assert(Mode == Util::TD::id<SizeMode::First>,
                          "Create::Private::flat does not support the given SizeMode");
            return simplify(Ex::factory<T>(sym, Op::factory<OpT>(std::move(operands)),
                                           Ex::get_bit_length(operands[0]), std::move(sp)));
        }
        else {
            static_assert(Mode == Util::TD::id<SizeMode::NA>,
                          "SizeMode should be NA for non-sized type");
            return simplify(
                Ex::factory<T>(sym, Op::factory<OpT>(std::move(operands)), std::move(sp)));
        }
    }

} // namespace Create::Private

#endif
