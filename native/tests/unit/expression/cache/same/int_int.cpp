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
int int_int() {
    Int a = literal_int();
    Int b = literal_int();
    if (a == b) {
        return 0;
    }
    else {
        return 1;
    }
}
