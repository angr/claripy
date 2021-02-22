/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the literal function compiles and can be run without issue */
void literal() {

    // Create inputs
    std::string data1 { "This is data!" };
    std::string data2 { data1 };
    const auto bl { 100 + BitLength::char_bit * data1.size() };

    // Test
    (void) Create::literal<Expression::Bool>(Create::EAnVec {}, std::move(data1));
    (void) Create::literal<Expression::BV>(Create::EAnVec {}, std::move(data2), bl);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(literal)
