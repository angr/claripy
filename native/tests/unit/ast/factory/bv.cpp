/** @file */

#include "ast/bv.hpp"

#include "testlib.hpp"

#include <set>


// For brevity
using namespace UnitTest::TestLib;


/** Test creating an AST::BV */
int bv() {
    (void) construct_ast<AST::BV>();
    return 0;
}
