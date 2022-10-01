/**
* @file
* @brief This file defines a method to create an Expr with an Eq Op
*/
#ifndef R_SRC_CREATE_FP_SQRT_HPP_
#define R_SRC_CREATE_FP_SQRT_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expr with a Sqrt op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr sqrt(const Mode::FP::Rounding mode, const Expr::BasePtr &fp, Expr::OpPyDict d = {}) {
        UTIL_ASSERT(Error::Expr::Usage, fp, "fp may not be nullptr");
        UTIL_ASSERT(Error::Expr::Type, CUID::is_t<Expr::FP>(fp), "fp must be an Expr::FP");
        const auto len { Expr::bit_length(fp) };
        return Simplify::simplify(Expr::factory<Expr::FP>(fp->symbolic, Op::factory<Op::FP::Sqrt>(mode, fp), std::move(d), len));
    }

} // namespace Create::FP

#endif