/**
 * @file
 * \ingroup testlib
 */
#include "verify.hpp"

#include "../error.hpp"


/** True if and only if test_func ran once */
static bool ran { false };


void UnitTest::TestLib::Private::verify() {
    UNITTEST_ASSERT_MSG(not ran, "UnitTest::TestLib::Private::verify() ran more than once");
    ran = true;
}


/** If not ran, throw an exception */
void fail_if_unverified() {
    UNITTEST_ASSERT_MSG(ran, "No test case ran via testlib");
}


/** Run fail_if_unverified after main */
UTIL_RUN_FUNCTION_AFTER_MAIN(fail_if_unverified)
