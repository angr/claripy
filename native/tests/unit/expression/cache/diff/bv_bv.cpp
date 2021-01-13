/** @file */

#include "testlib.hpp"

#include <set>

// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Test creating an AST::BV */
int bv_bv() {
    BV a = construct_ast<BV>((Op::Operation) 0);
    BV b = construct_ast<BV>((Op::Operation) 1);
    if (a != b) {
        return 0;
    }
    else {
        return 1;
    }
}
