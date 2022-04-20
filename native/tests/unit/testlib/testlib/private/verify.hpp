
/**
 * @file
 * @brief This file is used to verify that test_func ran exactly once
 * \ingroup testlib
 */
#ifndef R_TESTS_UNIT_TESTLIB_TESTLIB_PRIVATE_VERIFY_HPP_
#define R_TESTS_UNIT_TESTLIB_TESTLIB_PRIVATE_VERIFY_HPP_


namespace UnitTest::TestLib::Private {

    /** This function is called to verify that test_func was executed
     *  If this function does not run, a destructor will raise an exception after main exits
     */
    void verify();

} // namespace UnitTest::TestLib::Private

#endif
