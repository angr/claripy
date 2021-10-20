/**
 * @file
 * @brief This file defines a method to create Exprs with standard binary ops
 */
#ifndef R_CREATE_PRIVATE_UINTBINARY_HPP_
#define R_CREATE_PRIVATE_UINTBINARY_HPP_

#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with a uint binary op
     *  Expr pointers may not be nullptr
     */
    template <typename IntT, typename Out, typename In, typename OpT, SizeMode Mode,
              typename... Allowed>
    inline Expr::BasePtr uint_binary(const Expr::BasePtr &expr, const IntT integer,
                                     Annotation::SPAV &&sp) {
        namespace Ex = Expr;
        using namespace Simplification;
        namespace Err = Error::Expr;

        // Static checks
        static_assert(Util::qualified_is_in<IntT, UInt, Int>,
                      "Create::Private::uint_binary requires IntT be either UInt or "
                      "Int");
        static_assert(Util::is_ancestor<Ex::Base, Out>,
                      "Create::Private::uint_binary requires Out be an Expr");
        static_assert(Util::is_ancestor<Ex::Base, In>,
                      "Create::Private::uint_binary requires In be an Expr");
        static_assert(Op::is_uint_binary<OpT>,
                      "Create::Private::uint_binary requires a int binary OpT");
        if constexpr (Util::is_ancestor<Ex::Bits, Out>) {
            const constexpr bool sized_in { Util::is_ancestor<Ex::Bits, In> };
            static_assert(
                Util::TD::boolean<sized_in, In>,
                "Create::Private::uint_binary does not support sized output types without "
                "sized input types");
        }
        static_assert(Util::qualified_is_in<In, Allowed...>,
                      "Create::Private::uint_binary requires In is in Allowed");

        // Dynamic checks
        Util::affirm<Err::Usage>(expr != nullptr, WHOAMI_WITH_SOURCE "expr cannot be nullptr");
        Util::affirm<Err::Type>(CUID::is_t<In>(expr),
                                WHOAMI_WITH_SOURCE "Expr operand of incorrect type");

        // Construct expr (static casts are safe because of previous checks)
        if constexpr (Util::is_ancestor<Ex::Bits, Out>) {
            static_assert(Util::TD::boolean<Mode != SizeMode::NA, Out>,
                          "SizeMode::NA not allowed with sized output type");
            // Construct size
            UInt new_bit_length { integer };
            if constexpr (Mode == SizeMode::Add) {
                new_bit_length += Ex::get_bit_length(expr);
            }
            else if constexpr (Mode != SizeMode::Second) {
                static_assert(Util::TD::false_<Out>,
                              "Create::Private::uint_binary does not support the given SizeMode");
            }
            // Actually construct expr
            return simplify(Ex::factory<Out>(expr->symbolic, Op::factory<OpT>(expr, integer),
                                             new_bit_length, std::move(sp)));
        }
        else {
            static_assert(Mode == Util::TD::id<SizeMode::NA>,
                          "SizeMode should be NA for non-sized type");
            return simplify(
                Ex::factory<Out>(expr->symbolic, Op::factory<OpT>(expr, integer), std::move(sp)));
        }
    }

    /** Create a Expr with a uint binary op
     *  Expr pointers may not be nullptr
     *  A specialization where In = Out
     */
    template <typename IntT, typename InOut, typename OpT, SizeMode Mode, typename... Allowed>
    inline Expr::BasePtr uint_binary(const Expr::BasePtr &expr, const IntT integer,
                                     Annotation::SPAV &&sp) {
        return uint_binary<IntT, InOut, InOut, OpT, Mode, Allowed...>(expr, integer,
                                                                      std::move(sp));
    }

} // namespace Create::Private

#endif
