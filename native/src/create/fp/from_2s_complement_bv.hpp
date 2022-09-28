/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_SRC_CREATE_FP_FROM2SCOMPLEMENTBV_HPP_
#define R_SRC_CREATE_FP_FROM2SCOMPLEMENTBV_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expr with an From2sComplementBVSigned op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr from_2s_complement_bv_signed(const Mode::FP::Rounding m,
                                                      const Expr::BasePtr &bv,
                                                      const Mode::FP::Width &w,
                                                      Expr::OpPyDict d = {}) {
        UTIL_ASSERT(Error::Expr::Usage, bv, "bv may not be nullptr");
        using FromBV = Op::FP::From2sComplementBVSigned;
        return Simplify::simplify(Expr::factory<Expr::FP>(
            bv->symbolic, Op::factory<FromBV>(m, bv, w), std::move(d), w.width()));
    }

    /** Create an Expr with an From2sComplementBVUnigned op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr from_2s_complement_bv_unsigned(const Mode::FP::Rounding m,
                                                        const Expr::BasePtr &bv,
                                                        const Mode::FP::Width &w,
                                                        Expr::OpPyDict d = {}) {
        UTIL_ASSERT(Error::Expr::Usage, bv, "bv may not be nullptr");
        using FromBV = Op::FP::From2sComplementBVUnsigned;
        return Simplify::simplify(Expr::factory<Expr::FP>(
            bv->symbolic, Op::factory<FromBV>(m, bv, w), std::move(d), w.width()));
    }

} // namespace Create::FP

#endif
