/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** A moveable type */
struct Moveable {
    /** Constructor */
    Moveable(const int in) : x(in) {}
    /** Move constructor */
    Moveable(Moveable &&old) : x(old.x) {}
    /** Representation */
    const int x;
};

/** A macro used for consistency */
#define NEW_MOVE                                                                                  \
    Moveable { 0x1234 }

struct UnitTest::ClaricppUnitTest {
    /** Constructor */
    ClaricppUnitTest() : c {}, data { c.data }, dsize { c.dsize } {}
    /** The cache */
    Utils::ToHeapCache<Moveable> c;
    /** Extract data */
    const decltype(c.data) &data;
    /** Extract dsize */
    const Constants::UInt &dsize;
};

/** Verify the to_heap_cache members work */
void to_heap_cache() {

    // Variables
    UnitTest::ClaricppUnitTest cache;
    std::vector<Moveable *> heap;

    // Constructor test
    UNITTEST_ASSERT(cache.data.size() == cache.dsize)
    UNITTEST_ASSERT(cache.dsize > 4)

    // Verify cache is used
    for (Constants::UInt i = 0; i < cache.dsize / 2; ++i) {
        heap.push_back(cache.c.move_to_heap(NEW_MOVE));
    }
    auto dsize { cache.dsize - cache.dsize / 2 }; // If dsize is odd this isn't simply /2
    UNITTEST_ASSERT(cache.data.size() == dsize)

    // Verify free returns to cache
    for (Constants::UInt i = 0; i < cache.dsize / 4; ++i) {
        cache.c.free(heap.back());
        heap.pop_back();
    }
    dsize += cache.dsize / 4;
    UNITTEST_ASSERT(cache.data.size() == dsize)

    // Empty cache
    for (Constants::UInt i = 0; i < dsize; ++i) {
        heap.push_back(cache.c.move_to_heap(NEW_MOVE));
    }
    UNITTEST_ASSERT(cache.data.size() == 0)

    // Verify cache recreation when empty
    heap.push_back(cache.c.move_to_heap(NEW_MOVE));
    UNITTEST_ASSERT(cache.data.size() == cache.dsize)

    // Read each item on the heap (for memory checker testing)
    for (auto &i : heap) {
        UNITTEST_ASSERT(i->x == NEW_MOVE.x)
    }

    // Make cache larger than reserve size
    dsize = cache.data.size() + heap.size();
    while (heap.size() > 0) {
        cache.c.free(heap.back());
        heap.pop_back();
    }
    UNITTEST_ASSERT(cache.data.size() == dsize)
    UNITTEST_ASSERT(dsize > cache.dsize)

    // Verify downsize functions
    cache.c.downsize();
    UNITTEST_ASSERT(cache.data.size() == cache.dsize)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(to_heap_cache)
