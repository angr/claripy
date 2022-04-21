/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A cache */
static Util::WeakCache<int, int> cache;


/** Test creating two different items */
void diff() {
    const auto a { cache.find_or_emplace<int>(1, 1) };
    const auto b { cache.find_or_emplace<int>(2, 2) };
    UNITTEST_ASSERT(a != b);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(diff)
