/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef R_CREATE_FP_FROMFP_HPP_
#define R_CREATE_FP_FROMFP_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expression with an FromFP op
     *  Expression pointers may not be nullptr
     */
    inline EBasePtr from_fp(const Mode::FP::Rounding m, const EBasePtr &fp,
                            const Mode::FP::Width w, SPAV &&sp = nullptr) {
        Utils::affirm<Error::Expression::Usage>(fp != nullptr,
                                                WHOAMI_WITH_SOURCE "fp may not be nullptr");
        return Simplification::simplify(Expression::factory<Expression::FP>(
            fp->symbolic, Op::factory<Op::FP::FromFP>(m, fp, w), w.width(), std::move(sp)));
    }

} // namespace Create::FP

#endif
