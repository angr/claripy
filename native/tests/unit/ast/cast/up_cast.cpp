/** @file */

#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/* up_casting should succeed */
int up_cast() {
    Int a = construct_ast<Int>();
    Base b = up_cast<Base>(a);
    UNITTEST_ASSERT_MSG(b != nullptr, "This condition should be impossible to trigger"
                                      "If you see this message, something is very very wrong.");
    return 0;
}
