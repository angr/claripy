/**
 * @file
 * @brief This file includes all relevant public sections of testlib
 * \defgroup testlib Test Helper Library
 * @brief A library that contains common functions that unit teses may use
 */
#ifndef __TESTS_UNIT_TESTLIB_TESTLIB_DEFINETEST_HPP__
#define __TESTS_UNIT_TESTLIB_TESTLIB_DEFINETEST_HPP__

/** A macro to make setting a test easier */
#define DEFINE_TEST(X) UnitTest::TestLib::TestFN *const UnitTest::TestLib::test_func = (X);


namespace UnitTest::TestLib {

    /** The type of the test function */
    using TestFN = void();

    /** The test function pointer
     *  If not set, should give a linker error
     */
    extern TestFN *const test_func;
} // namespace UnitTest::TestLib

#endif
