/** @file */

#include "ast/base.hpp"
#include "testlib.hpp"
#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Two bases should be different */
int base_base() {
    Base a = construct_ast<Base>((Op::Operation) 0);
    Base b = construct_ast<Base>((Op::Operation) 1);
    if (a != b) {
        return 0;
    }
    else {
        return 1;
    }
}
