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
    /** Constructor 0 */
    A(const Hash::Hash &h) : FactoryMade { h, 0_ui } {}
    /** Constructor 1 */
    A(const Hash::Hash &h, const Constants::UInt) : FactoryMade { h, 0_ui } {}
    /** Constructor 2 */
    A(const Hash::Hash &h, const Constants::UInt, const Constants::UInt)
        : FactoryMade { h, 0_ui } {}
};

/** Verify that two identical A objects are the same */
void factory_constructors() {
    // Same
    const auto a00 = Factory::factory<A, A>();
    const auto a01 = Factory::factory<A, A>();
    UNITTEST_ASSERT(a00 == a01)
    // Diff
    const auto a10 = Factory::factory<A, A>(0_ui);
    UNITTEST_ASSERT(a00 != a10)
    const auto a20 = Factory::factory<A, A>(0_ui, 0_ui);
    UNITTEST_ASSERT(a00 != a20)
    UNITTEST_ASSERT(a10 != a20)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(factory_constructors)
