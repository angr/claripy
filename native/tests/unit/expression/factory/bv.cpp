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
void bv() {
    (void) literal_factory<ConcreteBVLiteral>(0_i);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(bv)
