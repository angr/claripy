/**
 * @file
 * \ingroup unittest
 */
#include <cstring>
#include <testlib/testlib.hpp>


/** Verify the file line hash macros work */
void strlen() {
    constexpr CCSC msg { "This is a test" };
    const constexpr auto n { Util::strlen(msg) };
    UNITTEST_ASSERT(n == std::strlen(msg));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(strlen)
