/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_SRC_CREATE_FP_FROMNOT2SCOMPLEMENTBV_HPP_
#define R_SRC_CREATE_FP_FROMNOT2SCOMPLEMENTBV_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expr with an FromNot2sComplementBV op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr from_not_2s_complement_bv(const Expr::BasePtr &bv,
                                                   const Mode::FP::Width &w,
                                                   Expr::OpPyDict d = {}) {
        UTIL_ASSERT(Error::Expr::Usage, bv, "bv may not be nullptr");
        using Not2s = Op::FP::FromNot2sComplementBV;
        return Simplify::simplify(Expr::factory<Expr::FP>(bv->symbolic, Op::factory<Not2s>(bv, w),
                                                          std::move(d), w.width()));
    }

} // namespace Create::FP

#endif
