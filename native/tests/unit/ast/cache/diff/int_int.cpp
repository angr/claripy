/** @file */

#include "ast/int.hpp"

#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Test creating an AST::Int */
int int_int() {
    Int a = construct_ast<Int>((Op::Operation) 0);
    Int b = construct_ast<Int>((Op::Operation) 1);
    if (a != b) {
        return 0;
    }
    else {
        return 1;
    }
}
