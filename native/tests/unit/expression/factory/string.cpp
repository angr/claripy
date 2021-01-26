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
void string() {
    (void) literal_factory<ConcreteStringLiteral>(0_i);
}

// Define the test
DEFINE_TEST(string)
