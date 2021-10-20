/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


// For brevity
using namespace UnitTest::TestLib;


/** A cache */
static Util::WeakCache<UInt, UInt> cache;


/** A struct used to give friend access to unittests */
struct UnitTest::ClaricppUnitTest {
    /** size_type abbreviation */
    using SizeType = decltype(cache)::CacheMap::size_type;
    /** Get the cache gc_resize */
    SizeType &gc_resize = cache.gc_resize;
    /** Get the cache size */
    static SizeType size() { return cache.cache.size(); }
};


/** Construct a range of different exprs */
auto construct_range(const UInt lb, const UInt ub) {
    std::vector<Factory::Ptr<UInt>> ret;
    ret.reserve(ub - lb);
    for (UInt i { lb }; i < ub; ++i) {
        ret.push_back(cache.find_or_emplace<UInt>(i, i));
    }
    return ret;
}


/** Ensure weak_ptrs are properly invalidated and removed by both gc and find */
void gc() {
    UnitTest::ClaricppUnitTest ut_cache;
    const auto init { ut_cache.gc_resize };
    UInt n { 0 };

    // Sanity check
    UNITTEST_ASSERT(init > 100);

    // Construct gc_resize more than half of init's UInts
    const auto num { (3 * init) / 4 - 1 };
    Util::Log::debug("Constructing ", num, " exprs");

    const auto hold { construct_range(n, num) };
    n += num;

    // Sanity check
    UNITTEST_ASSERT(init == ut_cache.gc_resize);

    // Create and destroy UInts until we have gc_resize bases
    {
        const auto remaining { init - num };
        Util::Log::debug("Constructing ", remaining, " ref-count=0 exprs");
        (void) construct_range(n, n + remaining);
        n += remaining;
    }

    // Sanity check then check cache size
    UNITTEST_ASSERT(init == ut_cache.gc_resize);
    UNITTEST_ASSERT(ut_cache.size() == init);

    // Construct another base to trigger a garbage collection
    Util::Log::debug("Constructing one more expr");
    (void) cache.find_or_emplace<UInt>(n, n);

    // Verify cache size and gc_size
    UNITTEST_ASSERT(ut_cache.size() == hold.size() + 1);
    UNITTEST_ASSERT(ut_cache.gc_resize > init);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(gc)
