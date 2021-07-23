/**
 * @file
 * @brief This file defines a method to create Expressions with standard binary ops
 */
#ifndef R_CREATE_PRIVATE_BINARY_HPP_
#define R_CREATE_PRIVATE_BINARY_HPP_

#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with a binary op
     *  Expression pointers may not be nullptr
     */
    template <typename Out, typename In, typename OpT, SizeMode Mode, typename... Allowed>
    inline EBasePtr binary(const EBasePtr &left, const EBasePtr &right, SPAV &&sp) {
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Static checks
        static_assert(Utils::is_ancestor<Ex::Base, Out>,
                      "Create::Private::binary requires Out be an Expression");
        static_assert(Utils::is_ancestor<Ex::Base, In>,
                      "Create::Private::binary requires In be an Expression");
        static_assert(Op::is_binary<OpT>, "Create::Private::binary requires a binary OpT");
        if constexpr (Utils::is_ancestor<Ex::Bits, Out>) {
            const constexpr bool sized_in { Utils::is_ancestor<Ex::Bits, In> };
            static_assert(Utils::TD::boolean<sized_in, In>,
                          "Create::Private::binary does not support sized output types without "
                          "sized input types");
        }
        static_assert(Utils::qualified_is_in<In, Allowed...>,
                      "Create::Private::binary requires In is in Allowed");

        // Dynamic checks
        Utils::affirm<Err::Usage>(left != nullptr && right != nullptr, WHOAMI_WITH_SOURCE
                                  "Expression pointer arguments may not be nullptr");
        Utils::affirm<Err::Type>(CUID::is_t<In>(left),
                                 WHOAMI_WITH_SOURCE "left operand of incorrect type");

        // Construct expression (static casts are safe because of previous checks)
        if constexpr (Utils::is_ancestor<Ex::Bits, Out>) {
            static_assert(Utils::TD::boolean<Mode != SizeMode::NA, Out>,
                          "SizeMode::NA not allowed with sized output type");
            // Construct size
            Constants::UInt new_bit_length { Ex::get_bit_length(left) };
            if constexpr (Mode == SizeMode::Add) {
                // Type check before size extraction
                Utils::affirm<Err::Type>(CUID::is_t<In>(right),
                                         WHOAMI_WITH_SOURCE "right operand of incorrect type");
                new_bit_length += Ex::get_bit_length(right);
            }
            else if constexpr (Mode != SizeMode::First) {
                static_assert(Utils::TD::false_<Out>,
                              "Create::Private::binary does not support the given SizeMode");
            }
            // Actually construct expression
            return simplify(Ex::factory<Out>(left->symbolic || right->symbolic,
                                             Op::factory<OpT>(left, right), new_bit_length,
                                             std::move(sp)));
        }
        else {
            static_assert(Mode == Utils::TD::id<SizeMode::NA>,
                          "SizeMode should be NA for non-sized type");
            return simplify(Ex::factory<Out>(left->symbolic || right->symbolic,
                                             Op::factory<OpT>(left, right), std::move(sp)));
        }
    }

    /** Create a Expression with a binary op
     *  Expression pointers may not be nullptr
     *  A specialization where In = Out
     */
    template <typename InOut, typename OpT, SizeMode Mode, typename... Allowed>
    inline EBasePtr binary(const EBasePtr &left, const EBasePtr &right, SPAV &&sp) {
        return binary<InOut, InOut, OpT, Mode, Allowed...>(left, right, std::move(sp));
    }

} // namespace Create::Private

#endif
