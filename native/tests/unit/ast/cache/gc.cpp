/** @file */

#include "src/ast/base.hpp"
#include "src/ast/factory.hpp"
#include "src/ops/operations_enum.hpp"

#include <set>


// For brevity
using namespace AST;


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
    return factory<T>(std::move(s), std::move((Ops::Operation) n));
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
    if (init < 100) {
        return 1;
    }

    // Construct gc_resize more than half of init's bases
    const auto num = (3 * init) / 4 - 1;

    auto hold = construct_range<Base>(n, num);
    n += num;

    // Sanity check
    if (init != cache.gc_resize) {
        return 1;
    }

    // Create and destroy Bases until we have gc_resize bases
    {
        const auto remaining = init - num;
        (void) construct_range<Base>(n, n + remaining);
        n += remaining;
    }

    // Sanity check
    if (init != cache.gc_resize) {
        return 1;
    }

    // Check cache size
    if (cache.size() != init) {
        return 1;
    }

    // Construct another base to trigger a garbage collection
    (void) construct<Base>(n++);

    // Verify cache size and gc_size
    if (cache.size() != hold.size() + 1) {
        return 1;
    }
    if (cache.gc_resize <= init) {
        return 1;
    }

    // Success
    return 0;
}
