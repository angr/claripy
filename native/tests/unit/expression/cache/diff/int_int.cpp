/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Test creating an Expression::Int */
void int_int() {
    Int a = literal_int(0_i);
    Int b = literal_int(1_i);
    UNITTEST_ASSERT(a != b)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(int_int)
