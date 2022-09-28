/**
 * @file
 * @brief This file defines a method to create Exprs with standard fp mode binary ops
 */
#ifndef R_SRC_CREATE_PRIVATE_MODEBINARY_HPP_
#define R_SRC_CREATE_PRIVATE_MODEBINARY_HPP_

#include "size_mode.hpp"

#include "../../mode.hpp"
#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with an mode binary op
     *  Expr pointers may not be nullptr
     */
    template <typename OpT>
    inline Expr::BasePtr mode_binary(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                     const Mode::FP::Rounding mode, Expr::OpPyDict &&d) {
        static_assert(Op::FP::is_mode_binary<OpT>,
                      "Create::Private::mode_binary requires OpT to be Op::FP::ModeBinary");
        UTIL_ASSERT(Error::Expr::Usage, left && right, "Expr pointers cannot be nullptr");
        UTIL_ASSERT(Error::Expr::Type, CUID::is_t<Expr::FP>(left),
                    "left operand must be of type Expr::FP");

        // Create expr
        return Simplify::simplify(Expr::factory<Expr::FP>(left->symbolic || right->symbolic,
                                                          Op::factory<OpT>(left, right, mode),
                                                          std::move(d), Expr::bit_length(left)));
    }

} // namespace Create::Private

#endif
