/**
 * @file
 * @brief This file defines a macro to create a test and run it
 * Note: this macro defines the main() function
 * \ingroup testlib
 */
#ifndef R_UNIT_TESTLIB_TESTLIB_MAIN_HPP_
#define R_UNIT_TESTLIB_TESTLIB_MAIN_HPP_

#include "test_func.hpp"


/** Toggle claricpp backtrace */
static inline void toggle_backtrace() {
#ifdef DEBUG
    Util::Log::info("Enabling backtrace...");
    Util::Err::Claricpp::toggle_backtrace(true);
#endif
}

/** Define the main function and use it to test a given function */
#define UNITTEST_DEFINE_MAIN_TEST(TFUNC)                                                           \
    /** Main function: test TFUNC */                                                               \
    int main() {                                                                                   \
        using namespace UnitTest::TestLib;                                                         \
        original_bk = Util::Log::Backend::get();                                                   \
        original_sty = Util::Log::Style::get();                                                    \
        toggle_backtrace();                                                                        \
        return test_func((TFUNC));                                                                 \
    }


#endif
