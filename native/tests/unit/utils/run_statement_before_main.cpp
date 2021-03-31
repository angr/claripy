/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"
#include "utils.hpp"


/** A global variable */
static int test_var { 0 };

// Run test_var = 4 before main
UTILS_RUN_STATEMENT_BEFORE_MAIN(test_var = 4);


/** Ensure f(4) was run before main */
void run_statement_before_main() {
    UNITTEST_ASSERT(test_var == 4);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(run_statement_before_main)
