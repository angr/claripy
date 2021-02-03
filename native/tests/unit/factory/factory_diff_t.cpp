/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** A factory constructable object */
struct A : public FactoryMade {
    FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(A)
    /** Constructor */
    A(const Hash::Hash &h, const int) : FactoryMade { h, 0 } {}
};

/** Verify that two identical A objects are the same */
void factory_diff_t() {
    const auto a1 = Factory::factory<A, A>(1);
    const auto a2 = Factory::factory<A, A>(2);
    UNITTEST_ASSERT(a1 != a2)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(factory_diff_t)
