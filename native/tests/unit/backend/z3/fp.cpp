/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"

#include <limits>


/** Test normal ops in claricpp
 *  @todo: Enable string symbol testing
 */
void fp() {
    namespace Ex = Expression;
    namespace C = Create;

    // The backend
    Backend::Z3::Z3 z3bk;

    // For brevity
    using NLF = std::numeric_limits<float>;
    using NLD = std::numeric_limits<double>;

    const auto fp_x { C::symbol<Ex::FP>("fp_x", Mode::FP::dbl.width()) };
    const auto fp_y { C::symbol<Ex::FP>("fp_y", Mode::FP::dbl.width()) };
    const auto nan { C::literal(std::numeric_limits<double>::quiet_NaN()) };

    // Verify the round trip changes nothing
    const auto test_id = [&z3bk](const Expression::BasePtr &&x) {
        return z3bk.abstract(z3bk.convert(x)) == x;
    };

    /**************************************************/
    /*                    Literals                    */
    /**************************************************/

    Utils::Log::debug("Sanity checks...");
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

    Utils::Log::debug("Testing 0...");
    UNITTEST_ASSERT(test_id(C::literal(0.)));
    UNITTEST_ASSERT(test_id(C::literal(-0.)));
    /* UNITTEST_ASSERT(test_id(C::literal(0.F))); */
    /* UNITTEST_ASSERT(test_id(C::literal(-0.F))); */

    Utils::Log::debug("Testing Inf...");
    UNITTEST_ASSERT(test_id(C::literal(NLD::infinity())));
    UNITTEST_ASSERT(test_id(C::literal(-NLD::infinity())));
    /* UNITTEST_ASSERT(test_id(C::literal(NLF::infinity()))); */
    /* UNITTEST_ASSERT(test_id(C::literal(-NLF::infinity()))); */

    Utils::Log::debug("Testing NaN...");
    UNITTEST_ASSERT(test_id(C::literal(NLD::quiet_NaN())));
    /* UNITTEST_ASSERT(test_id(C::literal(NLF::signaling_NaN()))); */

    Utils::Log::debug("Testing subnormals...");
    UNITTEST_ASSERT(test_id(C::literal(NLD::denorm_min())));
    UNITTEST_ASSERT(test_id(C::literal(-NLD::denorm_min())));
    UNITTEST_ASSERT(test_id(C::literal(NLF::denorm_min())));
    UNITTEST_ASSERT(test_id(C::literal(-NLF::denorm_min())));

    Utils::Log::debug("Testing normals...");
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

    /**************************************************/
    /*                    Trivial                     */
    /**************************************************/
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(fp)
