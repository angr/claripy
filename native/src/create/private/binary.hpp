/**
 * @file
 * @brief This file defines a method to create Expressions with standard binary ops
 */
#ifndef __CREATE_PRIVATE_BINARY_HPP__
#define __CREATE_PRIVATE_BINARY_HPP__

#include "size.hpp"
#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with a binary op */
    template <typename Out, typename In, typename OpT, SizeMode Mode, typename... Allowed>
    inline EBasePtr binary(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        static_assert(Utils::is_ancestor<Expression::Base, Out>,
                      "binary requires Out be an Expression");
        static_assert(Utils::is_ancestor<Expression::Base, In>,
                      "binary requires In be an Expression");
        static_assert(Op::is_binary<OpT>, "binary requires a binary OpT");
        if constexpr (Utils::is_ancestor<Expression::Bits, Out>) {
            const constexpr bool sized_in { Utils::is_ancestor<Expression::Bits, In> };
            static_assert(Utils::TD::boolean<sized_in, In>,
                          "Create::Private::binary does not suppot sized output types without "
                          "sized input types");
        }

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type check
        static_assert(Utils::qualified_is_in<In, Allowed...>,
                      "Create::Private::binary requires In is in Allowed");
        Utils::affirm<Err::Type>(Ex::is_t<In>(left),
                                 "Create::Private::binary left operands of incorrect type");

        // Construct expression (static casts are safe because of previous checks)
        if constexpr (Utils::is_ancestor<Ex::Bits, Out>) {
            // Construct size
            Constants::UInt esize { size(left) };
            if constexpr (Mode == SizeMode::Add) {
                esize += size(right);
            }
            else if constexpr (Mode != SizeMode::First) {
                static_assert(Utils::TD::false_<Mode>,
                              "Create::Private::binary does not support the given SizeMode");
            }
            // Actually construct expression
            return simplify(Ex::factory<Out>(std::forward<EAnVec>(av),
                                             left->symbolic || right->symbolic,
                                             Op::factory<OpT>(left, right), esize));
        }
        else {
            static_assert(Mode == Utils::TD::id<SizeMode::NA>,
                          "SizeMode should be NA for non-sized type");
            return simplify(Ex::factory<Out>(std::forward<EAnVec>(av),
                                             left->symbolic || right->symbolic,
                                             Op::factory<OpT>(left, right)));
        }
    }

    /** Create a Expression with a binary op
     *  A specialization where In = Out
     */
    template <typename InOut, typename OpT, SizeMode Mode, typename... Allowed>
    inline EBasePtr binary(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        return binary<InOut, InOut, OpT, Mode, Allowed...>(std::forward<EAnVec>(av), left, right);
    }

} // namespace Create::Private

#endif
