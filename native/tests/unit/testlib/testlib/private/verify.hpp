
/**
 * @file
 * @brief This file is used to verify that test_func ran exactly once
 * \ingroup testlib
 */
#ifndef __TESTS_UNIT_TESTLIB_TESTLIB_PRIVATE_VERIFY_HPP__
#define __TESTS_UNIT_TESTLIB_TESTLIB_PRIVATE_VERIFY_HPP__


namespace UnitTest::TestLib {

    /** The private methods of testlib */
    namespace Private {

        /** This function is called to verify that test_func was executed
         *  If this function does not run, a destructor will raise an exception after main exits
         */
        void verify();

    } // namespace Private

} // namespace UnitTest::TestLib

#endif
