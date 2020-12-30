/** @file */

#include "ast/factory.hpp"
#include "ast/int.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace UnitTest::TestLib;


/** Test creating an AST::Int */
int int_() {
    (void) construct_ast<AST::Int>();
    return 0;
}
