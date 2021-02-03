/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"
#include "utils.hpp"


union UnsafePun {
    char arr[sizeof(Constants::Int)];
    Constants::Int i;
};


/** Verify the file line hash macros work */
void type_pun() {

    // The message
    constexpr Constants::CCSC msg { "Under 16 bytes" };
    static_assert(Utils::strlen(msg) + 1 <= sizeof(Constants::Int),
                  WHOAMI_WITH_SOURCE " needs a shorter message.");

    // Create p
    UnsafePun p;
    p.i = 0;

    // Safe pun
    p.i = Utils::type_pun<Constants::Int>(msg);

    // Use unsafe pun in controlled context to verify safe pun
    UNITTEST_ASSERT(std::strcmp(p.arr, msg) == 0)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(type_pun)
