/** @file */

#include "testlib.hpp"

#include <set>


// For brevity
using namespace UnitTest::TestLib;


/** Test creating an AST::Bits */
int bits() {
    (void) construct_ast<AST::Bits>(0);
    return 0;
}
