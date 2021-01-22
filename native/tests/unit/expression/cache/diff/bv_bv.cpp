/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>

// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Test creating an Expression::BV */
int bv_bv() {
    BV a = literal_factory<ConcreteBVLiteral>(1_i);
    BV b = literal_factory<ConcreteBVLiteral>(0_i);
    if (a != b) {
        return 0;
    }
    else {
        return 1;
    }
}
