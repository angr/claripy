/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A factory constructable object */
struct TestFactory : public Factory::FactoryMade {
    FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(TestFactory);
    /** Constructor */
    TestFactory(const Hash::Hash &h) : FactoryMade { h, 0_ui } {}
};

/** Verify that two identical TestFactory objects are the same */
void factory_same_t() {
    const auto a1 = Factory::factory<TestFactory, TestFactory>();
    const auto a2 = Factory::factory<TestFactory, TestFactory>();
    UNITTEST_ASSERT(a1 == a2);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(factory_same_t)
