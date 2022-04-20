/**
 * @file
 * @brief This file defines items related to fpa width in z3
 */
#ifndef R_SRC_BACKEND_Z3_WIDTHTRANSLATION_HPP_
#define R_SRC_BACKEND_Z3_WIDTHTRANSLATION_HPP_

#include "constants.hpp"

#include "../../mode.hpp"


namespace Backend::Z3 {

    /** A function that returns a reference to an internal thread_local z3 fpa sort
     *  This sort is the z3 analog of the given Mode::FP::Width
     */
    static inline const z3::sort fp_width_to_z3_sort(z3::context &ctx, const Mode::FP::Width &w) {
        if (LIKELY(w == Mode::FP::dbl)) {
            return ctx.template fpa_sort<64>();
        }
        if (LIKELY(w == Mode::FP::flt)) { // Not else so the LIKELYs don't conflict
            return ctx.template fpa_sort<32>();
        }
        Util::Log::warning("Using non-standard fp sort: ", w);
        return ctx.fpa_sort(w.exp, w.mantissa);
    }

    /** Returns a Mode::FP::Width constructed from the given z3 sort */
    static inline Mode::FP::Width z3_sort_to_fp_width(const z3::sort &s) {
        UTIL_ASSERT(Util::Err::Usage, s.is_fpa(),
                    "called on z3::sort that is not of a floating point type");
        return { s.fpa_ebits(), s.fpa_sbits() };
    }

} // namespace Backend::Z3

#endif
