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
                                 const Mode::FP::Width &w, Annotation::SPAV sp = empty_spav) {
        UTIL_ASSERT(Error::Expr::Usage, fp != nullptr, "fp may not be nullptr");
        return Simplify::simplify(Expr::factory<Expr::FP>(
            fp->symbolic, Op::factory<Op::FP::FromFP>(m, fp, w), w.width(), std::move(sp)));
    }

} // namespace Create::FP

#endif
