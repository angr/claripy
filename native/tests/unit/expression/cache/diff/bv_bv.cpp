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
void bv_bv() {
    BV a = literal_factory<ConcreteBVLiteral>(1_i);
    BV b = literal_factory<ConcreteBVLiteral>(0_i);
    UNITTEST_ASSERT(a != b)
}

// Define the test
DEFINE_TEST(bv_bv)
