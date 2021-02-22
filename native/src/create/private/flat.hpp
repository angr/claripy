/**
 * @file
 * @brief This file defines a method to create Expressions with standard flat ops
 */
#ifndef __CREATE_PRIVATE_FLAT_HPP__
#define __CREATE_PRIVATE_FLAT_HPP__

#include "bit_length.hpp"
#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with a flat op */
    template <typename T, typename OpT, SizeMode Mode, typename... Allowed>
    inline EBasePtr flat(EAnVec &&av, typename OpT::OpContainer &&operands) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;
        using OpC = typename OpT::OpContainer;

        // Type check
        static_assert(Op::is_flat<OpT>, "Create::Private::flat requires OpT to be flat");
        static_assert(Utils::qualified_is_in<T, Allowed...>,
                      "Create::Private::flat argument types must be in Allowed");
        Utils::affirm<Err::Size>(operands.size() >= 2, WHOAMI_WITH_SOURCE "operands are empty.");
        Utils::affirm<Err::Type>(Ex::is_t<T>(operands[0]),
                                 WHOAMI_WITH_SOURCE "operands[0] is the wrong type");

        // Calculate simple sym
        bool sym { false };
        for (const auto &i : operands) {
            sym |= i->symbolic;
        }

        // Construct expression (static casts are safe because of previous checks)
        if constexpr (Utils::is_ancestor<Ex::Bits, T>) {
            static_assert(Mode == Utils::TD::id<SizeMode::First>,
                          "Create::Private::flat does not support the given SizeMode");
            return simplify(Ex::factory<T>(std::forward<EAnVec>(av), sym,
                                           Op::factory<OpT>(std::forward<OpC>(operands)),
                                           bit_length(operands[0])));
        }
        else {
            static_assert(Mode == Utils::TD::id<SizeMode::NA>,
                          "SizeMode should be NA for non-sized type");
            return simplify(Ex::factory<T>(std::forward<EAnVec>(av), sym,
                                           Op::factory<OpT>(std::forward<OpC>(operands))));
        }
    }

} // namespace Create::Private

#endif
