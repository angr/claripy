/** @file */

#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Hashing must take into account type differences */
int identical_base_int() {
    Base a = construct_ast<Base>();
    Int b = construct_ast<Int>();
    Base b2 = up_cast<Base>(b);
    UNITTEST_ASSERT(a != b2);
    return 0;
}
