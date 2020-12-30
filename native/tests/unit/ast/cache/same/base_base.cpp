/** @file */

#include "ast/base.hpp"

#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Two bases should be the same */
int base_base() {
    Base a = construct_ast<Base>();
    Base b = construct_ast<Base>();
    if (a == b) {
        return 0;
    }
    else {
        return 1;
    }
}
