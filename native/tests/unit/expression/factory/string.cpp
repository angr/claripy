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
    (void) literal_factory<ConcreteStringLiteral>(0_i, 0_i);
    return 0;
}
