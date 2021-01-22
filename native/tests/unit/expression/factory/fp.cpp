/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Test creating an Expression FP */
int fp() {
    (void) literal_factory<ConcreteFPLiteral>(0_i);
    return 0;
}
