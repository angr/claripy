/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_SRC_CREATE_FP_TOBV_HPP_
#define R_SRC_CREATE_FP_TOBV_HPP_

#include "../constants.hpp"


namespace Create::FP {

    /** Create an Expr with a ToBVSigned op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr to_bv_signed(const Mode::FP::Rounding mode, const Expr::BasePtr &fp,
                                      const U64 bit_length, Annotation::SPAV sp = empty_spav) {
        UTIL_ASSERT(Error::Expr::Usage, fp, "fp may not be nullptr");
        return Simplify::simplify(Expr::factory<Expr::BV>(
            fp->symbolic, Op::factory<Op::FP::ToBVSigned>(mode, fp), bit_length, std::move(sp)));
    }

    /** Create an Expr with a ToBVUnsigned op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr to_bv_unsigned(const Mode::FP::Rounding mode, const Expr::BasePtr &fp,
                                        const U64 bit_length, Annotation::SPAV sp = empty_spav) {
        UTIL_ASSERT(Error::Expr::Usage, fp, "fp may not be nullptr");
        return Simplify::simplify(Expr::factory<Expr::BV>(
            fp->symbolic, Op::factory<Op::FP::ToBVUnsigned>(mode, fp), bit_length, std::move(sp)));
    }

} // namespace Create::FP

#endif
