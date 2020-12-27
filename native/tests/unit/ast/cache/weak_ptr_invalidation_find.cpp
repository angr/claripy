/** @file */

#include "ast/base.hpp"
#include "ast/factory.hpp"
#include "ops/operations.hpp"

#include <set>


// For brevity
using namespace AST;


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


/** Construct a Base */
template <typename T> T construct() {
    std::set<BackendID> s;
    return factory<T>(std::move(s), std::move((Ops::Operation) 0));
}


/** Ensure weak_ptrs are properly invalidated and removed by both gc and find */
int weak_ptr_invalidation_find() {
    UnitTest::ClaricppUnitTest cache;

    // Create and destroy a base, but record its hash
    Hash id;
    {
        Base a = construct<Base>();
        id = a->id;
    }

    // Check cache size
    if (cache.size() != 1) {
        return 1;
    }

    // Find then verify size
    if (cache.unsafe_find(id) != nullptr) {
        return 1;
    }
    return cache.size();
}
