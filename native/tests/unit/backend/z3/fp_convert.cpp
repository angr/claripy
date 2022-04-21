/**
 * @file
 * \ingroup unittest
 */
#include "shim_z3.hpp"

#include <cmath>
#include <testlib/testlib.hpp>


/** Return true iff p evaluates to true */
inline bool is_true(UnitTest::Friend::ShimZ3 &z3, const Expr::BasePtr &p) {
    return z3.convert(p.get()).simplify().is_true();
}

/** Return true iff p evaluates to false */
inline bool is_false(UnitTest::Friend::ShimZ3 &z3, const Expr::BasePtr &p) {
    return z3.convert(p.get()).simplify().is_false();
}


/** Try to convert a claricpp expr to z3 */
void fp_convert() {
    namespace C = Create;

    UnitTest::Friend::ShimZ3 z3;
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
