/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A cache */
static Util::WeakCache<int, int> cache;


/** A struct used to give friend access to unittests */
struct UnitTest::Friend {
    /** Get the cache size */
    decltype(cache)::CacheMap::size_type size() { return cache.cache.size(); }
    /** Passthrough unsafe_gc */
    void unsafe_gc() { return cache.unsafe_gc(); }
};


/** Ensure weak_ptrs are properly invalidated and removed by gc */
void weak_ptr_invalidation_gc() {
    UnitTest::Friend ut_cache;

    // Create and destroy a base
    { (void) cache.find_or_emplace<int>(1, 1); }

    // Check cache size
    UNITTEST_ASSERT(ut_cache.size() == 1);

    // Garbage collect then verify size
    ut_cache.unsafe_gc();
    UNITTEST_ASSERT(ut_cache.size() == 0);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(weak_ptr_invalidation_gc)
