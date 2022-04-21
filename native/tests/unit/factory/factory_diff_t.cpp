/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A factory constructable object */
struct TestFactory : public Factory::FactoryMade {
    FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(TestFactory, 0);
    /** Constructor */
    TestFactory(const Hash::Hash &h, const U64) : FactoryMade { h, 0_ui } {}
};

/** Verify that two identical TestFactory objects are the same */
void factory_diff_t() {
    const auto a1 = Factory::factory<TestFactory, TestFactory>(1_ui);
    const auto a2 = Factory::factory<TestFactory, TestFactory>(2_ui);
    UNITTEST_ASSERT(a1 != a2);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(factory_diff_t)
