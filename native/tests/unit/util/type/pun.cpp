/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A raw union for testing type punning */
union UnsafePun {
    double d;
    uint64_t i;
};

static_assert(sizeof(uint64_t) == sizeof(double), "type_pun test needs to be changed");


/** Verify the file line hash macros work */
void pun() {
    constexpr double d { 432.5241342 }; // NOLINT
    uint64_t onto = 0;

    // Safe pun
    UTIL_TYPE_PUN_ONTO(&onto, &d); // NOLINT

    // Unsafe pun
    UnsafePun p; // NOLINT
    p.d = d;     // NOLINT (note that this also memsets 0)

    // Use unsafe pun in a controlled context to verify safe pun
    UNITTEST_ASSERT(p.i == onto); // NOLINT
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(pun)
