/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


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
    UTILS_RECURRENCE_GUARD_LIM(LIMIT);
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
    bool caught { false };
    try {
        loop(20); // NOLINT
    }
    catch (const RecurrenceLimit &e) {
        caught = true;
    }

    // Verify recurrence guard worked
    UNITTEST_ASSERT(caught);
    UNITTEST_ASSERT(count == LIMIT);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(recurrence_guard)
