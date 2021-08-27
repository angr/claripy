/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

/** Test if a and b average to c */
template <typename T> static bool test(const T a, const T b, const T c) {
    return c == Utils::avg(a, b);
}

/** Verify avg works */
void avg() {
    const auto maxu { std::numeric_limits<unsigned>::max() };
    const auto maxi { std::numeric_limits<int>::max() };
    const auto mini { std::numeric_limits<int>::min() };

    // Unsigned

    UNITTEST_ASSERT(test(1u, 3u, 2u));
    UNITTEST_ASSERT(test(1u, 4u, 2u));
    UNITTEST_ASSERT(test(1u, 5u, 3u));

    UNITTEST_ASSERT(test(0u, maxu, maxu / 2));

    // Int
    UNITTEST_ASSERT(test(1, 3, 2));
    UNITTEST_ASSERT(test(1, 4, 2)); // Round down
    UNITTEST_ASSERT(test(1, 5, 3));

    UNITTEST_ASSERT(test(-1, -3, -2));
    UNITTEST_ASSERT(test(-1, -4, -3)); // Round down
    UNITTEST_ASSERT(test(-1, -5, -3));

    UNITTEST_ASSERT(test(-1, 8, 3));  // Round down
    UNITTEST_ASSERT(test(1, -8, -4)); // Round down

    UNITTEST_ASSERT(test(maxi, mini, -1)); // Round down
    UNITTEST_ASSERT(test(maxi, mini + 1, 0));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(avg)
