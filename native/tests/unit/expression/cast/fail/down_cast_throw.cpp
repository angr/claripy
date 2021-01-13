/** @file */

#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Down casting should fail with an exception */
int down_cast_throw() {
    Bool a = construct_ast<Bool>();
    Base b = up_cast<Base>(a);
    try {
        Int c = down_cast_throw_on_fail<Int>(b);
    }
    catch (Utils::Error::Unexpected::BadCast &e) {
        return 0;
    }
    return 1;
}
