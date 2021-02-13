/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the literal function compiles and can be run without issue */
void literal() {

    // Test
    std::string data { "This is data!" };
    const auto size { 100 + data.size() };
    (void) Create::literal<Expression::BV>(Create::EAnVec {}, std::move(data), size);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(literal)
