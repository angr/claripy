/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


// For brevity
using namespace Util::Err;

// For consistency
#define LIMIT 10

/** A static count variable */
static unsigned count { 0 };

/** A recurrence guarded function that will recur N times
 *  Increments count each time
 */
void loop(unsigned n) {
    UTIL_RECURRENCE_GUARD_LIM(LIMIT);
    count += 1;
    if (n == 0) {
        return;
    }
    loop(n - 1);
    Util::Log::warning("End loop");
}

/** Ensure the recurrence guard works */
void recurrence_guard() {

    // Test recurrence guard
    try {
        loop(20); // NOLINT
        UNITTEST_ERR("The recurrence guard failed to trigger")
    }
    catch (const RecurrenceLimit &e) {
    }

    // Verify recurrence guard worked as expected
    UNITTEST_ASSERT(count == LIMIT);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(recurrence_guard)
