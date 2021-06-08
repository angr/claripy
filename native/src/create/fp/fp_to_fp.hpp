/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef R_CREATE_FP_FPTOFP_HPP_
#define R_CREATE_FP_FPTOFP_HPP_

#include "../constants.hpp"


namespace Create {

    /** Create an Expression with an ToBV op
     *  Expression pointers may not be nullptr
     */
    template <typename T, bool Signed>
    EBasePtr fp_to_fp(const Mode::FP::Rounding m, const EBasePtr &fp, const Mode::FP::Width w,
                      const Constants::UInt bit_length, SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        /* namespace Err = Error::Expression; */
        using namespace Simplification;

        // Checks
        static_assert(Utils::is_ancestor<Ex::Bits, T>, "T must subclass Expression::Bits");
        Utils::affirm<Error::Expression::Usage>(fp != nullptr,
                                                WHOAMI_WITH_SOURCE "fp may not be nullptr");
        /* Utils::affirm<Err::Type>(CUID::is_t<T>(fp), */
        /*                          WHOAMI_WITH_SOURCE "fp must be a T"); */


#if 1
        if is_bv (a1)
            and is_fp_sort(a2)
                : return FPRef(Z3_mk_fpa_to_fp_bv(ctx.ref(), a1.ast, a2.ast), ctx)
                      elif is_fprm(a1) and
                is_fp(a2) and
                is_fp_sort(a3)
                : return FPRef(Z3_mk_fpa_to_fp_float(ctx.ref(), a1.ast, a2.ast, a3.ast), ctx)
                      elif is_fprm(a1) and
                  is_real(a2) and
                  is_fp_sort(a3)
                : return FPRef(Z3_mk_fpa_to_fp_real(ctx.ref(), a1.ast, a2.ast, a3.ast), ctx)
                      elif is_fprm(a1) and
                  is_bv(a2) and
                  is_fp_sort(a3)
                : return FPRef(Z3_mk_fpa_to_fp_signed(ctx.ref(), a1.ast, a2.ast, a3.ast), ctx)
#endif

#if 0
        if constexpr (Utils::is_ancestor<Ex::Bits, Out>) {
            const constexpr bool sized_in { Utils::is_ancestor<Ex::Bits, In> };
            static_assert(Utils::TD::boolean<sized_in, In>,
                          "Create::Private::binary does not suppot sized output types without "
                          "sized input types");
        }
        static_assert(Utils::qualified_is_in<In, Allowed...>,
                      "Create::Private::binary requires In is in Allowed");


        namespace Ex = Expression;
        return Simplification::simplify(Ex::factory<Ex::BV>(
            fp->symbolic, Op::factory<Op::FP::ToBV<Signed>>(mode, fp), bit_length, std::move(sp)));
#endif
                      throw Utils::Error::Unexpected::NotImplemented("tbd");
    }

} // namespace Create

#endif
