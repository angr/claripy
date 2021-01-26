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
void bool_() {
    (void) literal_factory<ConcreteBoolLiteral>(static_cast<Constants::Int>(0));
}

// Define the test
DEFINE_TEST(bool_)
