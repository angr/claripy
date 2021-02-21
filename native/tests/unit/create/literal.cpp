/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the literal function compiles and can be run without issue */
void literal() {
    std::string data { "This is data!" };
    const auto bl { 100 + BitLength::char_bit * data.size() };
    (void) Create::literal<Expression::BV>(Create::EAnVec {}, std::move(data), bl);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(literal)
