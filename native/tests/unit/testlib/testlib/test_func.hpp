/**
 * @file
 * @brief This file defines a method to test a test function
 * \ingroup testlib
 */
#ifndef __TESTS_UNIT_TESTLIB_TESTLIB_TESTFUNC_HPP__
#define __TESTS_UNIT_TESTLIB_TESTLIB_TESTFUNC_HPP__


namespace UnitTest::TestLib {

    /** The test function type */
    using TestFN = void();

    /** A method to test a test function */
    int test_func(TestFN &f);

} // namespace UnitTest::TestLib


#endif
