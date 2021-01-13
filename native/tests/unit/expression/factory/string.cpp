/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Test creating an Expression String */
int string() {
    Constants::Int z = 0;
    (void) literal_factory<ConcreteStringLiteral>(z, z);
    return 0;
}
