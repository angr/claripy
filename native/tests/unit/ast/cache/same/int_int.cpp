/** @file */

#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Two ints should be the same */
int int_int() {
    Int a = construct_ast<Int>();
    Int b = construct_ast<Int>();
    if (a == b) {
        return 0;
    }
    else {
        return 1;
    }
}
