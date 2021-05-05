/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "create.hpp"
#include "testlib.hpp"

#include <cmath>


/** Try to create a new solver */
void solver() {
    auto z3 { Backend::Z3::Z3 {} };
    (void) z3.new_tls_solver();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(solver)
