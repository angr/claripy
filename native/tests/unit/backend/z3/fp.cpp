/**
 * @file
 * \ingroup unittest
 */
#include "shim_z3.hpp"

#include <limits>
#include <testlib/testlib.hpp>


/** Test normal ops in claricpp
 *  @todo: Enable string symbol testing
 */
void fp() {
    const auto tz { Mode::FP::Rounding::TowardsZero };
    namespace C = Create;

    // The backend
    UnitTest::Friend::ShimZ3 z3;

    // For brevity
    using NLF = std::numeric_limits<float>;
    using NLD = std::numeric_limits<double>;

    const auto bv_x { C::symbol_bv("bv_x", Mode::FP::dbl.width()) };
    const auto fp_x { C::symbol_fp("fp_x", Mode::FP::dbl.width()) };
    const auto fp_y { C::symbol_fp("fp_y", Mode::FP::dbl.width()) };
    const auto nan { C::literal(std::numeric_limits<double>::quiet_NaN()) };

    // Verify the round trip changes nothing
    const auto test_id = [&z3](const Expr::BasePtr &&x) {
        return z3.abstract(z3.convert(x.get())) == x;
    };

    /**************************************************/
    /*                    Literals                    */
    /**************************************************/

    Util::Log::debug("Sanity checks...");
    UNITTEST_ASSERT(NLD::has_signaling_NaN);
    UNITTEST_ASSERT(NLF::has_signaling_NaN);
    UNITTEST_ASSERT(NLD::has_quiet_NaN);
    UNITTEST_ASSERT(NLF::has_quiet_NaN);
    UNITTEST_ASSERT(NLD::has_infinity);
    UNITTEST_ASSERT(NLF::has_infinity);
    UNITTEST_ASSERT(NLD::has_denorm);
    UNITTEST_ASSERT(NLF::has_denorm);
    UNITTEST_ASSERT(NLD::is_iec559);
    UNITTEST_ASSERT(NLF::is_iec559);

    Util::Log::debug("Testing 0...");
    UNITTEST_ASSERT(test_id(C::literal(0.)));
    UNITTEST_ASSERT(test_id(C::literal(-0.)));
    UNITTEST_ASSERT(test_id(C::literal(0.F)));
    UNITTEST_ASSERT(test_id(C::literal(-0.F)));

    Util::Log::debug("Testing Inf...");
    UNITTEST_ASSERT(test_id(C::literal(NLD::infinity())));
    UNITTEST_ASSERT(test_id(C::literal(-NLD::infinity())));
    UNITTEST_ASSERT(test_id(C::literal(NLF::infinity())));
    UNITTEST_ASSERT(test_id(C::literal(-NLF::infinity())));

    Util::Log::debug("Testing NaN...");
    UNITTEST_ASSERT(test_id(C::literal(NLD::quiet_NaN())));
    UNITTEST_ASSERT(test_id(C::literal(NLF::quiet_NaN())));

    const auto test_snan = [&z3](const bool is_double) {
        const auto s { is_double ? C::literal(NLD::signaling_NaN())
                                 : C::literal(NLF::signaling_NaN()) };
        const auto *const op_s { dynamic_cast<CTSC<Op::Literal>>(s->op.get()) };
        UNITTEST_ASSERT(op_s != nullptr);
        // Verify cycled expr
        const auto cycled { z3.abstract(z3.convert(s.get())) };
        UNITTEST_ASSERT(Expr::are_same_type<true>(cycled, s));
        // Verify cycled op
        const auto *const op { dynamic_cast<CTSC<Op::Literal>>(cycled->op.get()) };
        UNITTEST_ASSERT(op != nullptr);
        // Verify cycled value
        if (is_double) {
            const auto *const d_ptr { std::get_if<double>(&(op->value)) };
            UNITTEST_ASSERT(d_ptr != nullptr);
            UNITTEST_ASSERT(std::isnan(*d_ptr));
        }
        else {
            const auto *const f_ptr { std::get_if<float>(&(op->value)) };
            UNITTEST_ASSERT(f_ptr != nullptr);
            UNITTEST_ASSERT(std::isnan(*f_ptr));
        }
        return true;
    };
    UNITTEST_ASSERT(test_snan(true));
    UNITTEST_ASSERT(test_snan(false));

    Util::Log::debug("Testing subnormals...");
    UNITTEST_ASSERT(test_id(C::literal(NLD::denorm_min())));
    UNITTEST_ASSERT(test_id(C::literal(-NLD::denorm_min())));
    UNITTEST_ASSERT(test_id(C::literal(NLF::denorm_min())));
    UNITTEST_ASSERT(test_id(C::literal(-NLF::denorm_min())));

    Util::Log::debug("Testing normals...");
    const std::vector<double> normals {
        .00001, .125, .5, .75, 1., 2., 4., 5., 34., 1209342.
    }; // NOLINT
    for (const double i : normals) {
        UNITTEST_ASSERT(test_id(C::literal(i)));
        UNITTEST_ASSERT(test_id(C::literal(-i)));
        UNITTEST_ASSERT(test_id(C::literal(float(i))));
        UNITTEST_ASSERT(test_id(C::literal(-float(i))));
    }

    /**************************************************/
    /*                  Non-Trivial                   */
    /**************************************************/

    Util::Log::debug("Testing to_bv...");
    UNITTEST_ASSERT(test_id(C::FP::to_bv_signed(tz, fp_x, Expr::get_bit_length(fp_x))));
    UNITTEST_ASSERT(test_id(C::FP::to_bv_unsigned(tz, fp_x, Expr::get_bit_length(fp_x))));

    Util::Log::debug("Testing from_fp...");
    /* UNITTEST_ASSERT(test_id(C::FP::from_fp(tz, fp_x, Mode::FP::dbl))); */

    Util::Log::debug("Testing from_2s_complement_bv...");
    /* UNITTEST_ASSERT(test_id(C::FP::from_2s_complement_bv<Sgnd::Signed>(tz, bv_x,
     * Mode::FP::dbl))); */
    /* UNITTEST_ASSERT(test_id(C::FP::from_2s_complement_bv<Sgnd::Unsigned>(tz, bv_x,
     * Mode::FP::dbl))); */

    Util::Log::debug("Testing from_not_2s_complement_bv...");
    /* UNITTEST_ASSERT(test_id(C::FP::from_not_2s_complement_bv(bv_x, Mode::FP::dbl))); */

    /**************************************************/
    /*                    Trivial                     */
    /**************************************************/

    Util::Log::debug("Testing to_ieee_bv...");
    UNITTEST_ASSERT(test_id(C::FP::to_ieee_bv(fp_x)));

    Util::Log::debug("Testing FP Add...");
    UNITTEST_ASSERT(test_id(C::FP::add(fp_x, fp_y, tz)));

    Util::Log::debug("Testing FP Sub...");
    UNITTEST_ASSERT(test_id(C::FP::sub(fp_x, fp_y, tz)));

    Util::Log::debug("Testing FP Mul...");
    UNITTEST_ASSERT(test_id(C::FP::mul(fp_x, fp_y, tz)));

    Util::Log::debug("Testing FP Div...");
    UNITTEST_ASSERT(test_id(C::FP::div(fp_x, fp_y, tz)));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(fp)
