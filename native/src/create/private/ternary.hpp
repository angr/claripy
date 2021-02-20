/**
 * @file
 * @brief This file defines a method to create Expressions with standard ternary ops
 */
#ifndef __CREATE_PRIVATE_TERNARY_HPP__
#define __CREATE_PRIVATE_TERNARY_HPP__

#include "size.hpp"
#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with a ternary op */
    template <typename Out, typename In, typename OpT, SizeMode Mode, typename... Allowed>
    inline EBasePtr ternary(EAnVec &&av, const EBasePtr &first, const EBasePtr &second,
                            const EBasePtr &third) {
        static_assert(Utils::is_ancestor<Expression::Base, Out>,
                      "Create::Private::ternary requires Out be an Expression");
        static_assert(Utils::is_ancestor<Expression::Base, In>,
                      "Create::Private::ternary requires In be an Expression");
        static_assert(Op::is_ternary<OpT>, "Create::Private::ternary requires a ternary OpT");
        if constexpr (Utils::is_ancestor<Expression::Bits, Out>) {
            const constexpr bool sized_in { Utils::is_ancestor<Expression::Bits, In> };
            static_assert(Utils::TD::boolean<sized_in, In>,
                          "Create::Private::ternary does not suppot sized output types without "
                          "sized input types");
        }

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type check
        static_assert(Utils::qualified_is_in<In, Allowed...>,
                      "Create::Private::ternary requires In is in Allowed");
        Utils::affirm<Err::Type>(Ex::is_t<In>(first),
                                 WHOAMI_WITH_SOURCE "first operand of incorrect type");

        // Construct expression (static casts are safe because of previous checks)
        if constexpr (Utils::is_ancestor<Ex::Bits, Out>) {
            static_assert(Utils::TD::boolean<Mode != SizeMode::NA, Out>,
                          "SizeMode::NA not allowed with sized output type");
            // Construct size
            Constants::UInt esize { size(first) };
            if constexpr (Mode == SizeMode::Add) {
                Utils::affirm<Err::Type>(Ex::is_t<In>(second),
                                         WHOAMI_WITH_SOURCE "second operand of incorrect type");
                Utils::affirm<Err::Type>(Ex::is_t<In>(third),
                                         WHOAMI_WITH_SOURCE "third operand of incorrect type");
                esize += size(second) + size(third);
            }
            else {
                static_assert(Utils::TD::false_<Out>,
                              "Create::Private::ternary does not support the given SizeMode");
            }
            // Actually construct expression
            return simplify(Ex::factory<Out>(
                std::forward<EAnVec>(av), first->symbolic || second->symbolic || third->symbolic,
                Op::factory<OpT>(first, second, third), esize));
        }
        else {
            static_assert(Mode == Utils::TD::id<SizeMode::NA>,
                          "SizeMode should be NA for non-sized type");
            return simplify(Ex::factory<Out>(
                std::forward<EAnVec>(av), first->symbolic || second->symbolic || third->symbolic,
                Op::factory<OpT>(first, second, third)));
        }
    }

    /** Create a Expression with a ternary op
     *  A specialization where In = Out
     */
    template <typename InOut, typename OpT, SizeMode Mode, typename... Allowed>
    inline EBasePtr ternary(EAnVec &&av, const EBasePtr &first, const EBasePtr &second,
                            const EBasePtr &third) {
        return ternary<InOut, InOut, OpT, Mode, Allowed...>(std::forward<EAnVec>(av), first,
                                                            second, third);
    }

} // namespace Create::Private

#endif
