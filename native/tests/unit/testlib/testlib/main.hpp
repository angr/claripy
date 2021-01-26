/**
 * @file
 * @brief This file defines a macro to create a test and run it
 * Note: this macro defines the main() function
 * \ingroup testlib
 */
#ifndef __TESTS_UNIT_TESTLIB_TESTLIB_MAIN_HPP__
#define __TESTS_UNIT_TESTLIB_TESTLIB_MAIN_HPP__

#include "test_func.hpp"


// TODO: UNITTEST_DEFINE_MAIN_TEST
/** Define the main function and use it to test a given function */
#define DEFINE_TEST(F)                                                                            \
    /** Main function: test F */                                                                  \
    int main() {                                                                                  \
        UnitTest::TestLib::test_func(F);                                                          \
        return 0;                                                                                 \
    }


#endif
