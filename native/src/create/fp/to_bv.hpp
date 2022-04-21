/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_SRC_CREATE_FP_TOBV_HPP_
#define R_SRC_CREATE_FP_TOBV_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expr with an ToBV op
     *  Expr pointers may not be nullptr
     */
    template <Mode::Signed Sgn>
    Expr::BasePtr to_bv(const Mode::FP::Rounding mode, const Expr::BasePtr &fp,
                        const U64 bit_length, Annotation::SPAV &&sp) {
        UTIL_ASSERT(Error::Expr::Usage, fp, "fp may not be nullptr");
        return Simplify::simplify(Expr::factory<Expr::BV>(
            fp->symbolic, Op::factory<Op::FP::ToBV<Sgn>>(mode, fp), bit_length, std::move(sp)));
    }

    /** A shortcut to to_bv<Signed>; exists for the API */
    inline Expr::BasePtr to_bv_signed(const Mode::FP::Rounding mode, const Expr::BasePtr &fp,
                                      const U64 bit_length, Annotation::SPAV sp = empty_spav) {
        return to_bv<Mode::Signed::Signed>(mode, fp, bit_length, std::move(sp));
    }

    /** A shortcut to to_bv<Unsigned>; exists for the API */
    inline Expr::BasePtr to_bv_unsigned(const Mode::FP::Rounding mode, const Expr::BasePtr &fp,
                                        const U64 bit_length, Annotation::SPAV sp = empty_spav) {
        return to_bv<Mode::Signed::Unsigned>(mode, fp, bit_length, std::move(sp));
    }

} // namespace Create::FP

#endif
