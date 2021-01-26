/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace UnitTest::TestLib;


/** Test creating an Expression::Int */
void int_() {
    (void) UnitTest::TestLib::literal_int();
}

// Define the test
DEFINE_TEST(int_)
