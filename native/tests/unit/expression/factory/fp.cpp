/** @file */

#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Test creating an Expression FP */
int fp() {
    Constants::Int z = 0;
    (void) literal_factory<ConcreteFPLiteral>(z, z);
    return 0;
}
