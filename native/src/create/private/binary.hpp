/**
 * @file
 * @brief This file defines a method to create Exprs with standard binary ops
 */
#ifndef R_CREATE_PRIVATE_BINARY_HPP_
#define R_CREATE_PRIVATE_BINARY_HPP_

#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with a binary op
     *  Expr pointers may not be nullptr
     */
    template <typename Out, typename In, typename OpT, SizeMode Mode, typename... Allowed>
    inline Expr::BasePtr binary(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                Annotation::SPAV &&sp) {
        namespace Ex = Expr;
        using namespace Simplification;
        namespace Err = Error::Expr;

        // Static checks
        static_assert(Util::is_ancestor<Ex::Base, Out>,
                      "Create::Private::binary requires Out be an Expr");
        static_assert(Util::is_ancestor<Ex::Base, In>,
                      "Create::Private::binary requires In be an Expr");
        static_assert(Op::is_binary<OpT>, "Create::Private::binary requires a binary OpT");
        if constexpr (Util::is_ancestor<Ex::Bits, Out>) {
            const constexpr bool sized_in { Util::is_ancestor<Ex::Bits, In> };
            static_assert(Util::TD::boolean<sized_in, In>,
                          "Create::Private::binary does not support sized output types without "
                          "sized input types");
        }
        static_assert(Util::qualified_is_in<In, Allowed...>,
                      "Create::Private::binary requires In is in Allowed");

        // Dynamic checks
        Util::affirm<Err::Usage>(left != nullptr && right != nullptr,
                                 WHOAMI "Expr pointer arguments may not be nullptr");
        Util::affirm<Err::Type>(CUID::is_t<In>(left), WHOAMI "left operand of incorrect type");

        // Construct expr (static casts are safe because of previous checks)
        if constexpr (Util::is_ancestor<Ex::Bits, Out>) {
            static_assert(Util::TD::boolean<Mode != SizeMode::NA, Out>,
                          "SizeMode::NA not allowed with sized output type");
            // Construct size
            UInt new_bit_length { Ex::get_bit_length(left) };
            if constexpr (Mode == SizeMode::Add) {
                // Type check before size extraction
                Util::affirm<Err::Type>(CUID::is_t<In>(right),
                                        WHOAMI "right operand of incorrect type");
                new_bit_length += Ex::get_bit_length(right);
            }
            else if constexpr (Mode != SizeMode::First) {
                static_assert(Util::TD::false_<Out>,
                              "Create::Private::binary does not support the given SizeMode");
            }
            // Actually construct expr
            return simplify(Ex::factory<Out>(left->symbolic || right->symbolic,
                                             Op::factory<OpT>(left, right), new_bit_length,
                                             std::move(sp)));
        }
        else {
            static_assert(Mode == Util::TD::id<SizeMode::NA>,
                          "SizeMode should be NA for non-sized type");
            return simplify(Ex::factory<Out>(left->symbolic || right->symbolic,
                                             Op::factory<OpT>(left, right), std::move(sp)));
        }
    }

    /** Create a Expr with a binary op
     *  Expr pointers may not be nullptr
     *  A specialization where In = Out
     */
    template <typename InOut, typename OpT, SizeMode Mode, typename... Allowed>
    inline Expr::BasePtr binary(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                Annotation::SPAV &&sp) {
        return binary<InOut, InOut, OpT, Mode, Allowed...>(left, right, std::move(sp));
    }

} // namespace Create::Private

#endif
