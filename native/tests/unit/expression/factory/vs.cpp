/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Test creating an Expression VS */
int vs() {
    (void) literal_factory<ConcreteVSLiteral>(0_i);
    return 0;
}
