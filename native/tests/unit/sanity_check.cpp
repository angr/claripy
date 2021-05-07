/**
 * @file
 * @brief Sanity checks that should pass
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Returns the passed argument by reference */
static Constants::UInt id_ref(const Constants::UInt &id) {
    return id;
}

/** A macro to help with testing */
#define TEST_TYPE(X)                                                                              \
    {                                                                                             \
        namespace F = UnitTest::TestLib::Factories;                                               \
        const auto s { Expression::X::static_cuid };                                              \
        UNITTEST_ASSERT(s == id_ref(Expression::X::static_cuid));                                 \
        UNITTEST_ASSERT(s == F::t_literal<Expression::X>(0)->cuid);                               \
    }

/** Test samoty checks */
void sanity_check() {

    // Expression::X::static_cuid is defined at compile time of the shared library
    // by template meta-programming. Since it is calculated only within header files
    // when this test is compiled the compiler will independent calculate a value
    // for it when included by this test case. Since this value is not calculated
    // in a trivial manner and depend on macros such as __FILE__, in this test we
    // verify that the test case's calculation is consistent with the shared library's
    // in order to test that the calculaton is reproducable and not so brittle
    // as to be dependent on directoy location, something __FILE__ normally does.
    TEST_TYPE(Bool);
    TEST_TYPE(String);
    TEST_TYPE(VS);
    TEST_TYPE(BV);
    TEST_TYPE(FP);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(sanity_check)
