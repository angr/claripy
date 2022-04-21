/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A function to to be run before main */
int f(int a = 0) {
    static int ret { 0 };
    if (a) {
        return (ret = a);
    }
    else {
        return ret;
    }
}

/** RunOnDestruction functions properly */
void run_on_destruction() {

    // Create a scope
    {
        // Set f(4) to run on destruction
        Util::RunOnDestruction rod { [&]() noexcept { f(4); } };

    } // End scope

    // Verify f(f) ran
    UNITTEST_ASSERT(f() == 4);

    // Create a scope
    {
        // Set f(1) to run on destruction then disable it
        Util::RunOnDestruction rod { [&]() noexcept { f(4); } };
        rod.disable();

    } // End scope

    // Verify f(1) did not run
    UNITTEST_ASSERT(f() == 4);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(run_on_destruction)
