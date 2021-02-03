/**
 * @file
 * \ingroup unittest
 */
#include "factory.hpp"
#include "testlib.hpp"


/** A factory constructable object */
struct A : public Factory::FactoryMade {
    DEFINE_STATIC_CUID
    FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(A)
    /** Constructor */
    A(const Hash::Hash &h, const Constants::UInt) : FactoryMade { h, 0_ui } {}
};

/** Verify that two identical A objects are the same */
void factory_diff_t() {
    const auto a1 = Factory::factory<A, A>(1_ui);
    const auto a2 = Factory::factory<A, A>(2_ui);
    UNITTEST_ASSERT(a1 != a2)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(factory_diff_t)
