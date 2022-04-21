/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Test if a and b average to c */
template <typename T> static bool test(const T a, const T b, const T c) {
    return c == Util::avg(a, b);
}

/** Verify avg works */
void avg() {
    const auto maxu { std::numeric_limits<unsigned>::max() };
    const auto maxi { std::numeric_limits<int>::max() };
    const auto mini { std::numeric_limits<int>::min() };

    // Unsigned

    UNITTEST_ASSERT(test(1U, 3U, 2U));
    UNITTEST_ASSERT(test(1U, 4U, 2U));
    UNITTEST_ASSERT(test(1U, 5U, 3U));

    UNITTEST_ASSERT(test(0U, maxu, maxu / 2));

    // I64
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
