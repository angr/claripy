/**
 * @file
 * @brief This file defines a macro to create a test and run it
 * Note: this macro defines the main() function
 * \ingroup testlib
 */
#ifndef R_TESTS_UNIT_TESTLIB_TESTLIB_MAIN_HPP_
#define R_TESTS_UNIT_TESTLIB_TESTLIB_MAIN_HPP_

#include "test_func.hpp"

#include <pybind11/embed.h>


/** Testlib init */
static inline void testlib_init() {
#ifndef CONSTANT_LOG_LEVEL
    UnitTest::TestLib::original_bk = Util::Log::Backend::get();
    UnitTest::TestLib::original_sty = Util::Log::Style::get();
    Util::Log::Level::set(Util::Log::Level::debug);
#endif
    // Init
    Util::Log::info("Preparing for unit test");
    Util::Err::Claricpp::toggle_backtrace(true);
    Util::Backtrace::handle_signals();
    pybind11::initialize_interpreter(false);
    Util::Log::info("Unit test preparations complete");
}

/** Define the main function and use it to test a given function */
#define UNITTEST_DEFINE_MAIN_TEST(TFUNC)                                                           \
    /** Main function: test TFUNC */                                                               \
    int main() {                                                                                   \
        testlib_init();                                                                            \
        return UnitTest::TestLib::test_func((TFUNC));                                              \
    }


#endif
