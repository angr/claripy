/** @file */

#include "ast/base.hpp"
#include "ast/factory.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** A struct used to give friend access to unittests */
struct UnitTest::ClaricppUnitTest {
    /** Get the cache size */
    decltype(AST::Private::factory_cache)::CacheMap::size_type size() {
        return AST::Private::factory_cache.cache.size();
    }
    /** Passthrough unsafe_gc */
    void unsafe_gc() { return AST::Private::factory_cache.unsafe_gc(); }
};


/** Ensure weak_ptrs are properly invalidated and removed by both gc and find */
int weak_ptr_invalidation_gc() {
    UnitTest::ClaricppUnitTest cache;

    // Create and destroy a base
    { Base a = construct_ast<Base>(); }

    // Check cache size
    UNITTEST_ASSERT(cache.size() == 1)

    // Garbage collect then verify size
    cache.unsafe_gc();
    return cache.size();
}
