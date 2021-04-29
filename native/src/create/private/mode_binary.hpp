/**
 * @file
 * @brief This file defines a method to create Expressions with standard fp mode binary ops
 */
#ifndef __CREATE_PRIVATE_MODEBINARY_HPP__
#define __CREATE_PRIVATE_MODEBINARY_HPP__

#include "size_mode.hpp"

#include "../../mode.hpp"
#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with an mode binary op */
    template <typename OpT, SizeMode Mode>
    inline EBasePtr mode_binary(EAnVec &&av, const Expression::BasePtr &left,
                                const Expression::BasePtr &right, const Mode::FP mode) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type check
        static_assert(Op::FP::is_mode_binary<OpT>,
                      "Create::Private::mode_binary requires OpT to be Op::FP::ModeBinary");
        Utils::affirm<Err::Type>(CUID::is_t<Ex::FP>(left), WHOAMI_WITH_SOURCE
                                 "left operands must be of type Expression::FP");

        // Create expression
        static_assert(Mode == SizeMode::First,
                      "Create::Private::mode_binary does not support the given SizeMode");
        return simplify(Ex::factory<Expression::FP>(
            std::forward<EAnVec>(av), left->symbolic || right->symbolic,
            Op::factory<OpT>(left, right, mode), Expression::get_bit_length(left)));
    }

} // namespace Create::Private

#endif
