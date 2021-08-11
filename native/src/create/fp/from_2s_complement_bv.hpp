/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef R_CREATE_FP_FROM2SCOMPLEMENTBV_HPP_
#define R_CREATE_FP_FROM2SCOMPLEMENTBV_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expression with an FromFP op
     *  Expression pointers may not be nullptr
     */
    template <bool Signed>
    EBasePtr from_2s_complement(const Mode::FP::Rounding m, const EBasePtr &bv,
                                const Mode::FP::Width &w, SPAV &&sp = nullptr) {
        Utils::affirm<Error::Expression::Usage>(bv != nullptr,
                                                WHOAMI_WITH_SOURCE "bv may not be nullptr");
        using FromBV = Op::FP::From2sComplementBV<Signed>;
        return Simplification::simplify(Expression::factory<Expression::FP>(
            bv->symbolic, Op::factory<FromBV>(m, bv, w), w.width(), std::move(sp)));
    }

} // namespace Create::FP

#endif
