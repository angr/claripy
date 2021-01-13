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
int int_int() {
    Int a = literal_int(0_i);
    Int b = literal_int(1_i);
    if (a != b) {
        return 0;
    }
    else {
        return 1;
    }
}
