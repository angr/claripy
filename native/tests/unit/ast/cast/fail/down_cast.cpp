/** @file */

#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Down casting should fail */
int down_cast() {
    Base a = construct_ast<Base>();
    Int b = down_cast<Int>(a);
    UNITTEST_ASSERT(b == nullptr)
    return 0;
}
