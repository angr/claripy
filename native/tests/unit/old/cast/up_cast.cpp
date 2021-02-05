/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/* up_casting should succeed */
void up_cast() {
    ConcreteIntLiteral a { literal_int() };
    Base b { up_cast<Base>(a) };
    UNITTEST_ASSERT_MSG(b != nullptr, "This condition should be impossible to trigger"
                                      "If you see this message, something is very very wrong.");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(up_cast)
