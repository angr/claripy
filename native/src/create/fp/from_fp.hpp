/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_CREATE_FP_FROMFP_HPP_
#define R_CREATE_FP_FROMFP_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expr with an FromFP op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr from_fp(const Mode::FP::Rounding m, const EBasePtr &fp,
                            const Mode::FP::Width &w, Annotation::SPAV &&sp = nullptr) {
        Util::affirm<Error::Expr::Usage>(fp != nullptr,
                                         WHOAMI_WITH_SOURCE "fp may not be nullptr");
        return Simplification::simplify(Expr::factory<Expr::FP>(
            fp->symbolic, Op::factory<Op::FP::FromFP>(m, fp, w), w.width(), std::move(sp)));
    }

} // namespace Create::FP

#endif
