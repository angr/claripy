/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


namespace UnitTest {
    /** A struct used to give friend access to unittests */
    struct ClaricppUnitTest {
        /** size_type abbreviation */
        using SizeType = decltype(AST::Private::factory_cache)::CacheMap::size_type;
        /** Get the cache gc_resize */
        SizeType &gc_resize = AST::Private::factory_cache.gc_resize;
        /** Get the cache size */
        SizeType size() { return AST::Private::factory_cache.cache.size(); }
    };
} // namespace UnitTest

/** Construct a Base */
template <typename T> T construct(const int n, std::set<BackendID> s = std::set<BackendID>()) {
    return factory<T>(std::move(s), std::move((Op::Operation) n));
}

/** Construct a range of Bases */
template <typename T>
std::vector<T> construct_range(const unsigned int lb, const unsigned int ub) {
    std::vector<T> ret;
    ret.reserve(ub - lb);
    for (unsigned int i = lb; i < ub; ++i) {
        ret.push_back(construct<T>(i));
    }
    return ret;
}


/** Ensure weak_ptrs are properly invalidated and removed by both gc and find */
int gc() {
    UnitTest::ClaricppUnitTest cache;
    const UnitTest::ClaricppUnitTest::SizeType init = cache.gc_resize;
    int n = 0;

    // Sanity check
    UNITTEST_ASSERT(init > 100);

    // Construct gc_resize more than half of init's bases
    const auto num = (3 * init) / 4 - 1;

    auto hold = construct_range<Bool>(n, num);
    n += num;

    // Sanity check
    UNITTEST_ASSERT(init == cache.gc_resize);

    // Create and destroy Bools until we have gc_resize bases
    {
        const auto remaining = init - num;
        (void) construct_range<Bool>(n, n + remaining);
        n += remaining;
    }

    // Sanity check then check cache size
    UNITTEST_ASSERT(init == cache.gc_resize);
    UNITTEST_ASSERT(cache.size() == init);

    // Construct another base to trigger a garbage collection
    (void) construct<Bool>(n++);

    // Verify cache size and gc_size
    UNITTEST_ASSERT(cache.size() == hold.size() + 1);
    UNITTEST_ASSERT(cache.gc_resize > init);

    // Success
    return 0;
}
