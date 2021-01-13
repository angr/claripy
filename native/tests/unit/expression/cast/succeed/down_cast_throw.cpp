/** @file */
#include "expression.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/* Down casting should succeed */
int down_cast_throw() {
    ConcreteIntLiteral a = literal_int();
    Base b = up_cast<Base>(a);
    IntLiteral c = down_cast_throw_on_fail<IntLiteral>(b);
    UNITTEST_ASSERT(c == a)
    return 0;
}
