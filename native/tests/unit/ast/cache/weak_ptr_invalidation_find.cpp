/** @file */

#include "ast/base.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


namespace UnitTest {
    /** A struct used to give friend access to unittests */
    struct ClaricppUnitTest {
        /** Get the cache size */
        decltype(AST::Private::factory_cache)::CacheMap::size_type size() {
            return AST::Private::factory_cache.cache.size();
        }
        /** Passthrough unsafe_find */
        Base unsafe_find(const Hash &h) { return AST::Private::factory_cache.unsafe_find(h); }
    };
} // namespace UnitTest


/** Ensure weak_ptrs are properly invalidated and removed by both gc and find */
int weak_ptr_invalidation_find() {
    UnitTest::ClaricppUnitTest cache;

    // Create and destroy a base, but record its hash
    Hash id;
    {
        Base a = construct_ast<Base>();
        id = a->id;
    }

    // Check cache and cache size
    UNITTEST_ASSERT(cache.size() == 1)
    UNITTEST_ASSERT(cache.unsafe_find(id) == nullptr);
    return cache.size();
}
