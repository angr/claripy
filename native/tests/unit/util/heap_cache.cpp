/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A moveable type */
struct Moveable {
  public:
    /** Constructor */
    Moveable(const int in) noexcept : x { in } {}
    /** Move constructor */
    Moveable(Moveable &&old) noexcept : x { old.x } {}
    /** Disable copy construction */
    Moveable(const Moveable &) = delete;
    /** Default destructor */
    ~Moveable() = default;
    // Rule of 5
    SET_IMPLICITS_OPERATORS(Moveable, delete);
    /** Representation */
    const int x; // NOLINT (false positive)
};

/** A macro used for consistency */
#define NEW_MOVE                                                                                   \
    Moveable {                                                                                     \
        0x1234                                                                                     \
    }

struct UnitTest::Friend {
    /** Constructor */
    Friend() : c {}, data { c.data }, dsize { decltype(c)::dsize } {}
    /** The cache */
    Util::HeapCache<Moveable> c; // NOLINT (false positive)
    /** Extract data */
    const decltype(c.data) &data; // NOLINT (false positive)
    /** Extract dsize */
    const U64 &dsize; // NOLINT (false positive)
};

/** Verify the to_heap_cache members work */
void to_heap_cache() {

    // Variables
    UnitTest::Friend cache;
    std::vector<Moveable *> heap;

    // Constructor test
    UNITTEST_ASSERT(cache.data.size() == cache.dsize);
    UNITTEST_ASSERT(cache.dsize > 4);

    // Verify cache is used
    for (U64 i = 0; i < cache.dsize / 2; ++i) {
        heap.push_back(cache.c.move_to_heap(NEW_MOVE));
    }
    auto dsize { cache.dsize - cache.dsize / 2 }; // If dsize is odd this isn't simply /2
    UNITTEST_ASSERT(cache.data.size() == dsize);

    // Verify free returns to cache
    for (U64 i = 0; i < cache.dsize / 4; ++i) {
        cache.c.free(heap.back());
        heap.pop_back();
    }
    dsize += cache.dsize / 4;
    UNITTEST_ASSERT(cache.data.size() == dsize);

    // Empty cache
    for (U64 i = 0; i < dsize; ++i) {
        heap.push_back(cache.c.move_to_heap(NEW_MOVE));
    }
    UNITTEST_ASSERT(cache.data.empty());

    // Verify cache recreation when empty
    heap.push_back(cache.c.move_to_heap(NEW_MOVE));
    UNITTEST_ASSERT(cache.data.size() == cache.dsize);

    // Read each item on the heap (for memory checker testing)
    for (auto &i : heap) {
        UNITTEST_ASSERT(i->x == NEW_MOVE.x);
    }

    // Make cache larger than reserve size
    dsize = cache.data.size() + heap.size();
    while (not heap.empty()) {
        cache.c.free(heap.back());
        heap.pop_back();
    }
    UNITTEST_ASSERT(cache.data.size() == dsize);
    UNITTEST_ASSERT(dsize > cache.dsize);

    // Verify downsize functions
    cache.c.downsize();
    UNITTEST_ASSERT(cache.data.size() == cache.dsize);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(to_heap_cache)
