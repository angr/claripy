/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"
#include "utils.hpp"


/** A function to to be run before main */
int f(int a = 0) {
    static int ret = 0;
    if (a != 0) {
        return (ret = a);
    }
    else {
        return ret;
    }
}


// Run f(4) before main
UTILS_RUN_FUNCTION_BEFORE_MAIN(f, 4);


/** Ensure f(4) was run before main */
void run_function_before_main() { UNITTEST_ASSERT(f() == 4) }

// Define the test
DEFINE_TEST(run_function_before_main)
