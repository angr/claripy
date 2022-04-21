/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Verify that the Symbol class works */
void symbol() {
    // Names
    std::string n1 { "name1" };
    std::string n2 { n1 };
    std::string n3 { "name2" };
    // Construct
    const auto s1 = Op::factory<Op::Symbol>(std::move(n1));
    const auto s2 = Op::factory<Op::Symbol>(std::move(n2));
    const auto s3 = Op::factory<Op::Symbol>(std::move(n3));
    // Verify factory works
    UNITTEST_ASSERT(s1 == s2);
    UNITTEST_ASSERT(s1 != s3);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(symbol)
