/**
 * @file
 * @brief This file defines a method to create Expressions with standard flat ops
 */
#ifndef R_CREATE_PRIVATE_FLAT_HPP_
#define R_CREATE_PRIVATE_FLAT_HPP_

#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with a flat op
     *  operands' pointers may not be nullptr
     */
    template <typename T, typename OpT, SizeMode Mode, typename... Allowed>
    inline EBasePtr flat(typename OpT::OpContainer &&operands, Annotation::SPAV &&sp) {
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Checks
        static_assert(Op::is_flat<OpT>, "Create::Private::flat requires OpT to be flat");
        static_assert(Utils::qualified_is_in<T, Allowed...>,
                      "Create::Private::flat argument types must be in Allowed");
#ifdef DEBUG
        for (const auto &i : operands) {
            Utils::affirm<Err::Usage>(i != nullptr,
                                      WHOAMI_WITH_SOURCE "operands' pointers cannot be nullptrs");
        }
#endif
        Utils::affirm<Err::Size>(operands.size() >= 2, WHOAMI_WITH_SOURCE "operands are empty.");
        Utils::affirm<Err::Type>(CUID::is_t<T>(operands[0]),
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
            return simplify(Ex::factory<T>(sym, Op::factory<OpT>(std::move(operands)),
                                           Ex::get_bit_length(operands[0]), std::move(sp)));
        }
        else {
            static_assert(Mode == Utils::TD::id<SizeMode::NA>,
                          "SizeMode should be NA for non-sized type");
            return simplify(
                Ex::factory<T>(sym, Op::factory<OpT>(std::move(operands)), std::move(sp)));
        }
    }

} // namespace Create::Private

#endif
