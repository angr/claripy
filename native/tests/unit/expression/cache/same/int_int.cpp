/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Two ints should be the same */
void int_int() {
    Int a { literal_int() };
    Int b { literal_int() };
    UNITTEST_ASSERT(a == b)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(int_int)
