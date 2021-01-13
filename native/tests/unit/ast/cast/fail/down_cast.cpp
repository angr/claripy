/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Down casting should fail */
int down_cast() {
    Bool a = construct_ast<Bool>();
    Base b = up_cast<Base>(a);
    Int c = down_cast<Int>(b);
    UNITTEST_ASSERT(c == nullptr)
    return 0;
}
