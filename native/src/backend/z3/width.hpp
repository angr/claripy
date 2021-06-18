/**
 * @file
 * @brief This file defines items related to fpa width in z3
 */
#ifndef R_BACKEND_Z3_WIDTH_HPP_
#define R_BACKEND_Z3_WIDTH_HPP_

#include "tl_ctx.hpp"

#include "../../mode.hpp"


namespace Backend::Z3 {

    /** A z3 fpa single precision sort
     *  We prefer this to z3's pre-defined to ensure that exp and mantissa match
     */
    inline thread_local z3::sort z3_flt { Private::tl_ctx.template fpa_sort<32>() };

    /** A z3 fpa single precision sort
     *  We prefer this to z3's pre-defined to ensure that exp and mantissa match
     */
    inline thread_local z3::sort z3_dbl { Private::tl_ctx.template fpa_sort<64>() };

    /** A function that returns a reference to an internal thread_local z3 fpa sort
     *  This sort is the z3 analog of the given Mode::FP::Width
     *  Warning: This function *may* return the same reference on repeated infocations; that is
     *  repeated invocations of this function may overwrite the result of the previous reference
     */
    inline const z3::sort &unsafe_fp_width_to_z3_sort(const Mode::FP::Width &w) {
        if (LIKELY(w == Mode::FP::dbl)) {
            return z3_dbl;
        }
        if (LIKELY(w == Mode::FP::flt)) { // Not else so the LIKELYs don't conflict
            return z3_flt;
        }
        static thread_local z3::sort ret { Private::tl_ctx };
        ret = Private::tl_ctx.fpa_sort(w.exp, w.mantissa);
        return ret;
    }

    /** Returns a Mode::FP::Width constructed from the given z3 sort */
    inline const Mode::FP::Width z3_sort_to_fp_width(const z3::sort &s) {
        Utils::affirm<Utils::Error::Unexpected::Usage>(
            s.is_fpa(),
            WHOAMI_WITH_SOURCE "called on z3::sort that is not of a floating point type");
        return { s.fpa_ebits(), s.fpa_sbits() };
    }

} // namespace Backend::Z3

#endif
