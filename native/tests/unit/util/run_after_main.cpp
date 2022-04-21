/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A function which fails this tese case after main */
[[noreturn]] static void err() {
    // Print backtrace
    try {
        UNITTEST_ERR("This should have been disabled");
    }
    catch (UnitTest::TestLib::Error &) {
    }
    // Exit 1 since raising the exception after main won't change main's exit code
    std::exit(1);
}

/** A list of variables to be used by run after main checks */
std::vector<Util::RunOnDestruction<decltype(err)>> errors {};

// Prevent errors from triggering after main
// Note that we do each one twice to check for namespace collisions
UTIL_RUN_STATEMENT_AFTER_MAIN(errors[0].disable());
UTIL_RUN_STATEMENT_AFTER_MAIN(errors[1].disable());
UTIL_RUN_FUNCTION_AFTER_MAIN([]() { errors[2].disable(); });
UTIL_RUN_FUNCTION_AFTER_MAIN([]() { errors[3].disable(); });


/** Test running statements after main */
void run_after_main() {
    for (int i { 0 }; i < 4; ++i) {
        errors.emplace_back(err);
        UNITTEST_ASSERT(errors.back().status()); // Ensure each ROD is enabled
    }
    UNITTEST_ASSERT(errors.size() == 4); // Sanity check
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(run_after_main)
