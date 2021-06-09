/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef R_CREATE_FP_FROMNOT2SCOMPLEMENT_HPP_
#define R_CREATE_FP_FROMNOT2SCOMPLEMENT_HPP_

#include "../constants.hpp"


namespace Create {

    /** Create an Expression with an FromNot@sComplementBV op
     *  Expression pointers may not be nullptr
     */
    inline EBasePtr from_not_2s_complement(const EBasePtr &bv, const Mode::FP::Width w,
                                           SPAV &&sp = nullptr) {
        Utils::affirm<Error::Expression::Usage>(bv != nullptr,
                                                WHOAMI_WITH_SOURCE "bv may not be nullptr");
        using Not2s = Op::FP::FromNot2sComplementBV;
        return Simplification::simplify(Expression::factory<Expression::FP>(
            bv->symbolic, Op::factory<Not2s>(bv, w), w.width(), std::move(sp)));
    }

} // namespace Create

#endif
