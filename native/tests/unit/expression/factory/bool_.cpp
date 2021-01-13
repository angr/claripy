/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Test creating an Expression Bool */
int bool_() {
    (void) literal_factory<ConcreteBoolLiteral>((Constants::Int) 0);
    return 0;
}
