/** @file */

#include "ast/base.hpp"
#include "ast/cast.hpp"
#include "ast/factory.hpp"
#include "ast/int.hpp"
#include "op/operations.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/* Down casting should succeed */
int down_cast() {
    Int a = construct_ast<Int>();
    Base b = up_cast<Base>(a);
    Int c = down_cast<Int>(a);
    UNITTEST_ASSERT(c == a)
    return 0;
}
