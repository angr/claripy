/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


// Run Before Main

/** A global variable */
static std::set<int> test_set {};

// Insert values to test_set
// Note that we do each one twice to check for namespace collisions
UTIL_RUN_STATEMENT_BEFORE_MAIN(test_set.insert(0));
UTIL_RUN_STATEMENT_BEFORE_MAIN(test_set.insert(1));
UTIL_RUN_FUNCTION_BEFORE_MAIN([]() { test_set.insert(2); });
UTIL_RUN_FUNCTION_BEFORE_MAIN([]() { test_set.insert(3); });


/** Test running statements before main */
void run_before_main() {
    UNITTEST_ASSERT(test_set.size() == 4);
    const std::set<int> desired { 0, 1, 2, 3 };
    UNITTEST_ASSERT(test_set == desired);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(run_before_main)
