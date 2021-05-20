/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "dcast.hpp"
#include "testlib.hpp"


/** Verify that the extract<T> function compiles and can be run without issue */
template <typename T> void extract_t() {

    // For brevity
    namespace Ex = Expression; // NOLINT (false positive)

    // Create distinct inputs
    const Constants::UInt high { 2 };
    const Constants::UInt low { 2 };
    const auto a { UnitTest::TestLib::Factories::t_literal<T>(0) };

    // Test
    const auto exp { Create::extract<T>(high, low, a) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto op_down { dcast<Op::Extract>(exp->op) };
    const auto exp_down { dcast<T>(exp) };
    const auto a_down { dcast<T>(a) };

    // Contains check
    UNITTEST_ASSERT(op_down->from == a);

    // Size check
    UNITTEST_ASSERT(exp_down->bit_length == high + 1 - low);
}

/** Verify that the extract function compiles and can be run without issue */
void extract() {
    extract_t<Expression::BV>();
    extract_t<Expression::String>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(extract)
