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
    EBasePtr to_bv(const Mode::FP mode, const Expression::BasePtr &fp,
                   const Constants::UInt bit_length, SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        return Simplification::simplify(Ex::factory<Ex::BV>(
            fp->symbolic, Op::factory<Op::FP::ToBV<Signed>>(mode, fp), bit_length, std::move(sp)));
    }

} // namespace Create

#endif
