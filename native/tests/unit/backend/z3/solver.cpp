/**
 * @file
 * \ingroup unittest
 */
#include <cmath>
#include <testlib/testlib.hpp>


/** Try to create a new solver */
void solver() {
    auto z3 { Backend::Z3::Z3 {} };
    (void) z3.tls_solver();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(solver)
