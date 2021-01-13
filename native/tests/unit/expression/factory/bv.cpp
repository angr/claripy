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
    (void) literal_factory<ConcreteBVLiteral>(0_i, 0_i);
    return 0;
}
