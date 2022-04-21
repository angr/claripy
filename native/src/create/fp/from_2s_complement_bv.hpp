/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_SRC_CREATE_FP_FROM2SCOMPLEMENTBV_HPP_
#define R_SRC_CREATE_FP_FROM2SCOMPLEMENTBV_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expr with an FromFP op
     *  Expr pointers may not be nullptr
     */
    template <Mode::Signed Sgn>
    Expr::BasePtr from_2s_complement_bv(const Mode::FP::Rounding m, const Expr::BasePtr &bv,
                                        const Mode::FP::Width &w, Annotation::SPAV &&sp) {
        UTIL_ASSERT(Error::Expr::Usage, bv, "bv may not be nullptr");
        using FromBV = Op::FP::From2sComplementBV<Sgn>;
        return Simplify::simplify(Expr::factory<Expr::FP>(
            bv->symbolic, Op::factory<FromBV>(m, bv, w), w.width(), std::move(sp)));
    }

    /* A shortcut for from_2s_complement_bv; exists for the API */
    inline Expr::BasePtr from_2s_complement_bv_signed(const Mode::FP::Rounding m,
                                                      const Expr::BasePtr &bv,
                                                      const Mode::FP::Width &w,
                                                      Annotation::SPAV sp = empty_spav) {
        return from_2s_complement_bv<Mode::Signed::Signed>(m, bv, w, std::move(sp));
    }

    /* A shortcut for from_2s_complement_bv; exists for the API */
    inline Expr::BasePtr from_2s_complement_bv_unsigned(const Mode::FP::Rounding m,
                                                        const Expr::BasePtr &bv,
                                                        const Mode::FP::Width &w,
                                                        Annotation::SPAV sp = empty_spav) {
        return from_2s_complement_bv<Mode::Signed::Unsigned>(m, bv, w, std::move(sp));
    }

} // namespace Create::FP

#endif
