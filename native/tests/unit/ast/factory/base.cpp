/** @file */

#include "testlib.hpp"

#include <set>


// For brevity
using namespace UnitTest::TestLib;


/** Test creating an AST::Base */
int base() {
    (void) construct_ast<AST::Base>();
    return 0;
}
