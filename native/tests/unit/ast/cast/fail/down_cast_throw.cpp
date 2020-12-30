/** @file */

#include "ast/base.hpp"
#include "ast/cast.hpp"
#include "ast/int.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Down casting should fail with an exception */
int down_cast_throw() {
    Base a = construct_ast<Base>();
    try {
        Int b = down_cast_throw_on_fail<Int>(a);
    }
    catch (Utils::Error::Unexpected::BadCast &e) {
        return 0;
    }
    return 1;
}
