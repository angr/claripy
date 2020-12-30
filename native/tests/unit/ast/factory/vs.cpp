/** @file */

#include "ast/vs.hpp"

#include "ast/factory.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace UnitTest::TestLib;


/** Test creating an AST::VS */
int vs() {
    (void) construct_ast<AST::VS>();
    return 0;
}
