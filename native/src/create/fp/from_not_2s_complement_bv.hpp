/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_CREATE_FP_FROMNOT2SCOMPLEMENTBV_HPP_
#define R_CREATE_FP_FROMNOT2SCOMPLEMENTBV_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expr with an FromNot2sComplementBV op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr from_not_2s_complement(const Expr::BasePtr &bv, const Mode::FP::Width &w,
                                                Annotation::SPAV &&sp = nullptr) {
        Util::affirm<Error::Expr::Usage>(bv != nullptr,
                                         WHOAMI_WITH_SOURCE "bv may not be nullptr");
        using Not2s = Op::FP::FromNot2sComplementBV;
        return Simplification::simplify(Expr::factory<Expr::FP>(
            bv->symbolic, Op::factory<Not2s>(bv, w), w.width(), std::move(sp)));
    }

} // namespace Create::FP

#endif
