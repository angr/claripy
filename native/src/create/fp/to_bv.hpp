/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef R_CREATE_FP_TOBV_HPP_
#define R_CREATE_FP_TOBV_HPP_

#include "../constants.hpp"


namespace Create {

    /** Create an Expression with an ToBV op
     *  Expression pointers may not be nullptr
     */
    template <bool Signed>
    EBasePtr to_bv(const Mode::FP mode, const EBasePtr &fp, const Constants::UInt bit_length,
                   SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        Utils::affirm<Error::Expression::Usage>(fp != nullptr,
                                                WHOAMI_WITH_SOURCE "fp may not be nullptr");
        return Simplification::simplify(Ex::factory<Ex::BV>(
            fp->symbolic, Op::factory<Op::FP::ToBV<Signed>>(mode, fp), bit_length, std::move(sp)));
    }

} // namespace Create

#endif
