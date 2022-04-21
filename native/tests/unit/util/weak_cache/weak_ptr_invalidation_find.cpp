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
    /** Passthrough unsafe_find */
    auto unsafe_find(const int h) { return cache.unsafe_find(h); }
};


/** Ensure weak_ptrs are properly invalidated and removed by find */
void weak_ptr_invalidation_find() {
    UnitTest::Friend ut_cache;

    // Create and destroy an int
    const constexpr int hash { 1 };
    { (void) cache.find_or_emplace<int>(hash, 1); }

    // Check cache size
    UNITTEST_ASSERT(ut_cache.size() == 1);

    // Verify inability to find: side effect removes from cache
    const auto nll { ut_cache.unsafe_find(hash) };
    UNITTEST_ASSERT(nll == nullptr);

    // Check cache size
    UNITTEST_ASSERT(ut_cache.size() == 0);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(weak_ptr_invalidation_find)
