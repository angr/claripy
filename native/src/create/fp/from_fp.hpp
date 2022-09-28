/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_SRC_CREATE_FP_FROMFP_HPP_
#define R_SRC_CREATE_FP_FROMFP_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expr with an FromFP op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr from_fp(const Mode::FP::Rounding m, const Expr::BasePtr &fp,
                                 const Mode::FP::Width &w, Expr::OpPyDict d = {}) {
        UTIL_ASSERT(Error::Expr::Usage, fp, "fp may not be nullptr");
        return Simplify::simplify(Expr::factory<Expr::FP>(
            fp->symbolic, Op::factory<Op::FP::FromFP>(m, fp, w), std::move(d), w.width()));
    }

} // namespace Create::FP

#endif
