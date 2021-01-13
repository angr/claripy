/** @file */

#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Two bools should be different */
int bool_bool() {
    Bool a = construct_ast<Bool>((Op::Operation) 0);
    Bool b = construct_ast<Bool>((Op::Operation) 1);
    if (a != b) {
        return 0;
    }
    else {
        return 1;
    }
}
