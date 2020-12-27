/** @file */

#include "ast/fp.hpp"

#include "ast/factory.hpp"
#include "ops/operations.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace UnitTest::TestLib;


/** Test creating an AST::FP */
int fp() {
    (void) construct_ast<AST::FP>();
    return 0;
}
