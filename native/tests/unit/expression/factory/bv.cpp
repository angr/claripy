/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Test creating an Expression BV */
int bv() {
    Constants::Int z = 0;
    (void) literal_factory<ConcreteBVLiteral>(z, z);
    return 0;
}
