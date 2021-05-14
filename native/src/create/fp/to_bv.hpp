/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef R_CREATE_FP_TOBV_HPP_
#define R_CREATE_FP_TOBV_HPP_

#include "../constants.hpp"


namespace Create {

    /** Create an Expression with an ToBV op */
    template <bool Signed>
    EBasePtr to_bv(EAnVec &&av, const Mode::FP mode, const Expression::BasePtr &fp,
                   const Constants::UInt bit_length) {
        namespace Ex = Expression;
        return Simplification::simplify(
            Ex::factory<Ex::BV>(std::forward<EAnVec>(av), fp->symbolic,
                                Op::factory<Op::FP::ToBV<Signed>>(mode, fp), bit_length));
    }

} // namespace Create

#endif
