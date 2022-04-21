/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A factory constructable object */
struct TestFactory : public Factory::FactoryMade {
    FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(TestFactory, 0);
    /** Constructor 0 */
    TestFactory(const Hash::Hash &h) : FactoryMade { h, 0_ui } {}
    /** Constructor 1 */
    TestFactory(const Hash::Hash &h, const U64) : FactoryMade { h, 0_ui } {}
    /** Constructor 2 */
    TestFactory(const Hash::Hash &h, const U64, const U64) : FactoryMade { h, 0_ui } {}
};

/** Verify that two identical A objects are the same */
void factory_constructors() {
    // Same
    const auto a00 = Factory::factory<TestFactory, TestFactory>();
    const auto a01 = Factory::factory<TestFactory, TestFactory>();
    UNITTEST_ASSERT(a00 == a01);
    // Diff
    const auto a10 = Factory::factory<TestFactory, TestFactory>(0_ui);
    UNITTEST_ASSERT(a00 != a10);
    const auto a20 = Factory::factory<TestFactory, TestFactory>(0_ui, 0_ui);
    UNITTEST_ASSERT(a00 != a20);
    UNITTEST_ASSERT(a10 != a20);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(factory_constructors)
