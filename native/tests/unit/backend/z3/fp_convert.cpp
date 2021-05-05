/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "create.hpp"
#include "testlib.hpp"

#include <cmath>


/** Try to convert a claricpp expression to z3 */
void fp_convert() {
    namespace Ex = Expression;
    using AV = Ex::Base::AnVec;
    namespace C = Create;

    auto z3 { Backend::Z3::Z3 {} };
    auto solver { z3.new_tls_solver() };

    // Test with Nan
    const auto nan { C::literal(AV {}, std::numeric_limits<double>::quiet_NaN()) };
    const auto nan_is_nan { C::FP::is_nan(AV {}, nan) };
    const auto nan_is_inf { C::FP::is_inf(AV {}, nan) };

    Utils::Log::critical(z3.convert(nan_is_nan.get()));

    UNITTEST_ASSERT(z3.is_true(nan_is_nan.get(), solver, {}));
    UNITTEST_ASSERT(z3.is_false(nan_is_inf.get(), solver, {}));

    // Test with Inf
    const auto inf { C::literal(AV {}, std::numeric_limits<double>::infinity()) };
    const auto inf_is_nan { C::FP::is_nan(AV {}, inf) };
    const auto inf_is_inf { C::FP::is_inf(AV {}, inf) };
    UNITTEST_ASSERT(z3.is_false(inf_is_nan.get(), solver, {}));
    UNITTEST_ASSERT(z3.is_true(inf_is_inf.get(), solver, {}));

    // Test float
    const auto flt { C::literal(AV {}, 0.f) }; // NOLINT
    const auto flt_conv { z3.convert(flt.get()) };
    const auto srt { flt_conv.get_sort() };
    const Backend::Z3::FP::Width fpa_srt {
        srt.fpa_ebits(),
        srt.fpa_sbits(),
    };
    UNITTEST_ASSERT(fpa_srt == Backend::Z3::FP::flt);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(fp_convert)
