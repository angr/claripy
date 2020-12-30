/** @file */

#include "ast/bool.hpp"
#include "ast/factory.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace UnitTest::TestLib;


/** Test creating an AST::Bool */
int bool_() {
    (void) construct_ast<AST::Bool>();
    return 0;
}
