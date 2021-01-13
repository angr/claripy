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
    Constants::Int z = 0;
    (void) literal_factory<ConcreteVSLiteral>(z, z);
    return 0;
}
