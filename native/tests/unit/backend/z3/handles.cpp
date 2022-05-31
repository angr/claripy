/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Verify z3's handles() works */
void handles() {
    Backend::Z3::Z3 z3;

    const auto one { Create::literal(1_ui) };
    UNITTEST_ASSERT(z3.handles(one.get()));

    const auto vs { UnitTest::TestLib::Factories::t_literal<Expr::VS>(1) };
    UNITTEST_ASSERT(not z3.handles(vs.get()));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(handles)
