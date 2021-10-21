/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_CREATE_FP_FROM2SCOMPLEMENTBV_HPP_
#define R_CREATE_FP_FROM2SCOMPLEMENTBV_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expr with an FromFP op
     *  Expr pointers may not be nullptr
     */
    template <bool Signed>
    Expr::BasePtr from_2s_complement(const Mode::FP::Rounding m, const Expr::BasePtr &bv,
                                     const Mode::FP::Width &w, Annotation::SPAV &&sp = nullptr) {
        Util::affirm<Error::Expr::Usage>(bv != nullptr, WHOAMI "bv may not be nullptr");
        using FromBV = Op::FP::From2sComplementBV<Signed>;
        return Simplification::simplify(Expr::factory<Expr::FP>(
            bv->symbolic, Op::factory<FromBV>(m, bv, w), w.width(), std::move(sp)));
    }

} // namespace Create::FP

#endif
