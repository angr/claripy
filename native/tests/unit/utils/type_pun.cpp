/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"
#include "utils.hpp"


union UnsafePun {
    char arr[sizeof(Constants::Int) + 1]; // NOLINT
    Constants::Int i;
};


/** Verify the file line hash macros work */
void type_pun() {

    // The message
    constexpr Constants::CCSC msg { "Short" };
    static_assert(Utils::strlen(msg) + 1 <= sizeof(Constants::Int),
                  __FILE__ " needs a shorter message.");

    // Create p
    UnsafePun p; // NOLINT
    p.i = 0;     // NOLINT (note that this also memsets 0)

    // Safe pun
    UTILS_TYPE_PUN_ONTO(Constants::Int, &p.i, msg, true); // NOLINT

    // Use unsafe pun in controlled context to verify safe pun
    // Since we memset to 0, and msg is strictly shorter than arr, arr is null-terminated
    UNITTEST_ASSERT(std::strcmp(p.arr, msg) == 0); // NOLINT

    // Check other pun macros
    UTILS_TYPE_PUN_(Constants::Int, tmp, msg, true); // NOLINT
    UNITTEST_ASSERT(p.i == tmp);                     // NOLINT
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(type_pun)
