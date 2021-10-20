/**
 * @file
 * @brief This file defines a method to create Expressions with standard binary ops
 */
#ifndef R_CREATE_PRIVATE_UINTBINARY_HPP_
#define R_CREATE_PRIVATE_UINTBINARY_HPP_

#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with a uint binary op
     *  Expression pointers may not be nullptr
     */
    template <typename IntT, typename Out, typename In, typename OpT, SizeMode Mode,
              typename... Allowed>
    inline EBasePtr uint_binary(const EBasePtr &expr, const IntT integer, Annotation::SPAV &&sp) {
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Static checks
        static_assert(Utils::qualified_is_in<IntT, Constants::UInt, Constants::Int>,
                      "Create::Private::uint_binary requires IntT be either Constants::UInt or "
                      "Constants::Int");
        static_assert(Utils::is_ancestor<Ex::Base, Out>,
                      "Create::Private::uint_binary requires Out be an Expression");
        static_assert(Utils::is_ancestor<Ex::Base, In>,
                      "Create::Private::uint_binary requires In be an Expression");
        static_assert(Op::is_uint_binary<OpT>,
                      "Create::Private::uint_binary requires a int binary OpT");
        if constexpr (Utils::is_ancestor<Ex::Bits, Out>) {
            const constexpr bool sized_in { Utils::is_ancestor<Ex::Bits, In> };
            static_assert(
                Utils::TD::boolean<sized_in, In>,
                "Create::Private::uint_binary does not support sized output types without "
                "sized input types");
        }
        static_assert(Utils::qualified_is_in<In, Allowed...>,
                      "Create::Private::uint_binary requires In is in Allowed");

        // Dynamic checks
        Utils::affirm<Err::Usage>(expr != nullptr, WHOAMI_WITH_SOURCE "expr cannot be nullptr");
        Utils::affirm<Err::Type>(CUID::is_t<In>(expr),
                                 WHOAMI_WITH_SOURCE "Expression operand of incorrect type");

        // Construct expression (static casts are safe because of previous checks)
        if constexpr (Utils::is_ancestor<Ex::Bits, Out>) {
            static_assert(Utils::TD::boolean<Mode != SizeMode::NA, Out>,
                          "SizeMode::NA not allowed with sized output type");
            // Construct size
            Constants::UInt new_bit_length { integer };
            if constexpr (Mode == SizeMode::Add) {
                new_bit_length += Ex::get_bit_length(expr);
            }
            else if constexpr (Mode != SizeMode::Second) {
                static_assert(Utils::TD::false_<Out>,
                              "Create::Private::uint_binary does not support the given SizeMode");
            }
            // Actually construct expression
            return simplify(Ex::factory<Out>(expr->symbolic, Op::factory<OpT>(expr, integer),
                                             new_bit_length, std::move(sp)));
        }
        else {
            static_assert(Mode == Utils::TD::id<SizeMode::NA>,
                          "SizeMode should be NA for non-sized type");
            return simplify(
                Ex::factory<Out>(expr->symbolic, Op::factory<OpT>(expr, integer), std::move(sp)));
        }
    }

    /** Create a Expression with a uint binary op
     *  Expression pointers may not be nullptr
     *  A specialization where In = Out
     */
    template <typename IntT, typename InOut, typename OpT, SizeMode Mode, typename... Allowed>
    inline EBasePtr uint_binary(const EBasePtr &expr, const IntT integer, Annotation::SPAV &&sp) {
        return uint_binary<IntT, InOut, InOut, OpT, Mode, Allowed...>(expr, integer,
                                                                      std::move(sp));
    }

} // namespace Create::Private

#endif
