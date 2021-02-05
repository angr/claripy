/**
 * @file
 * \ingroup unittest
 */
#include "expression.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/* Down casting should succeed */
void down_cast_throw() {
    ConcreteIntLiteral a { literal_int() };
    Base b { up_cast<Base>(a) };
    IntLiteral c { down_cast_throw_on_fail<IntLiteral>(b) };
    UNITTEST_ASSERT(c == a)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(down_cast_throw)
