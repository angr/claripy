/**
 * @file
 * @brief This file defines a method to test a test function
 * \ingroup testlib
 */
#ifndef R_TESTS_UNIT_TESTLIB_TESTLIB_TESTFUNC_HPP_
#define R_TESTS_UNIT_TESTLIB_TESTLIB_TESTFUNC_HPP_


namespace UnitTest::TestLib {

    /** The test function type */
    using TestFN = void();

    /** A method to test a test function */
    int test_func(TestFN &f);

} // namespace UnitTest::TestLib


#endif
