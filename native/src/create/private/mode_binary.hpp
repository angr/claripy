/**
 * @file
 * @brief This file defines a method to create Exprs with standard fp mode binary ops
 */
#ifndef R_CREATE_PRIVATE_MODEBINARY_HPP_
#define R_CREATE_PRIVATE_MODEBINARY_HPP_

#include "size_mode.hpp"

#include "../../mode.hpp"
#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with an mode binary op
     *  Expr pointers may not be nullptr
     */
    template <typename OpT, SizeMode Mode>
    inline Expr::BasePtr mode_binary(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                     const Mode::FP::Rounding mode, Annotation::SPAV &&sp) {
        namespace Ex = Expr;
        using namespace Simplification;
        namespace Err = Error::Expr;

        // Checks
        static_assert(Op::FP::is_mode_binary<OpT>,
                      "Create::Private::mode_binary requires OpT to be Op::FP::ModeBinary");
        static_assert(Mode == SizeMode::First,
                      "Create::Private::mode_binary does not support the given SizeMode");
        Util::affirm<Err::Usage>(left != nullptr && right != nullptr,
                                 WHOAMI_WITH_SOURCE "Expr pointers cannot be nullptr");
        Util::affirm<Err::Type>(CUID::is_t<Ex::FP>(left),
                                WHOAMI_WITH_SOURCE "left operands must be of type Expr::FP");

        // Create expr
        return simplify(Ex::factory<Ex::FP>(left->symbolic || right->symbolic,
                                            Op::factory<OpT>(left, right, mode),
                                            Ex::get_bit_length(left), std::move(sp)));
    }

} // namespace Create::Private

#endif
