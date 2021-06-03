/**
 * @file
 * @brief This file defines a method to create Expressions with standard fp mode binary ops
 */
#ifndef R_CREATE_PRIVATE_MODEBINARY_HPP_
#define R_CREATE_PRIVATE_MODEBINARY_HPP_

#include "size_mode.hpp"

#include "../../mode.hpp"
#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with an mode binary op
     *  Expression pointers may not be nullptr
     */
    template <typename OpT, SizeMode Mode>
    inline EBasePtr mode_binary(const EBasePtr &left, const EBasePtr &right, const Mode::FP mode,
                                SPAV &&sp) {
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Checks
        static_assert(Op::FP::is_mode_binary<OpT>,
                      "Create::Private::mode_binary requires OpT to be Op::FP::ModeBinary");
        static_assert(Mode == SizeMode::First,
                      "Create::Private::mode_binary does not support the given SizeMode");
        Utils::affirm<Err::Usage>(left != nullptr && right != nullptr,
                                  WHOAMI_WITH_SOURCE "Expression pointers cannot be nullptr");
        Utils::affirm<Err::Type>(CUID::is_t<Ex::FP>(left), WHOAMI_WITH_SOURCE
                                 "left operands must be of type Expression::FP");

        // Create expression
        return simplify(Ex::factory<Ex::FP>(left->symbolic || right->symbolic,
                                            Op::factory<OpT>(left, right, mode),
                                            Ex::get_bit_length(left), std::move(sp)));
    }

} // namespace Create::Private

#endif
