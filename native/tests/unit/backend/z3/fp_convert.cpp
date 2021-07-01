/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "create.hpp"
#include "testlib.hpp"

#include <cmath>


/** Return true iff p evaluates to true */
inline bool is_true(Backend::Z3::Z3 &z3, const Expression::BasePtr &p) {
    return z3.convert(p.get()).simplify().is_true();
}

/** Return true iff p evaluates to false */
inline bool is_false(Backend::Z3::Z3 &z3, const Expression::BasePtr &p) {
    return z3.convert(p.get()).simplify().is_false();
}


/** Try to convert a claricpp expression to z3 */
void fp_convert() {
    namespace C = Create;

    auto z3 { Backend::Z3::Z3 {} };
    const auto flt { C::literal(0.f) }; // NOLINT
    const auto flt_conv { z3.convert(flt.get()) };
    const auto srt { flt_conv.get_sort() };
    const Mode::FP::Width fpa_srt {
        srt.fpa_ebits(),
        srt.fpa_sbits(),
    };

    UNITTEST_ASSERT(fpa_srt == Mode::FP::flt);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(fp_convert)
