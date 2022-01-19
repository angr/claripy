/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_CREATE_FP_TOBV_HPP_
#define R_CREATE_FP_TOBV_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expr with an ToBV op
     *  Expr pointers may not be nullptr
     */
    template <bool Signed>
    Expr::BasePtr to_bv(const Mode::FP::Rounding mode, const Expr::BasePtr &fp,
                        const UInt bit_length, Annotation::SPAV &&sp = nullptr) {
        UTIL_ASSERT(Error::Expr::Usage, fp != nullptr, "fp may not be nullptr");
        return Simplify::simplify(Expr::factory<Expr::BV>(
            fp->symbolic, Op::factory<Op::FP::ToBV<Signed>>(mode, fp), bit_length, std::move(sp)));
    }

} // namespace Create::FP

#endif
