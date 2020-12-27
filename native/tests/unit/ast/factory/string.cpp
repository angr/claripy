/** @file */

#include "ast/string.hpp"

#include "ast/factory.hpp"
#include "ops/operations.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace UnitTest::TestLib;


/** Test creating an AST::String */
int string() {
    (void) construct_ast<AST::String>();
    return 0;
}
