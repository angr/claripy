/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Hashing must take into account type differences */
void identical_bool_int() {
    auto a { literal_factory<ConcreteIntLiteral>(0_i) };
    auto b { literal_factory<ConcreteBoolLiteral>(0_i) };
    Base a2 { up_cast<Base>(a) };
    Base b2 { up_cast<Base>(b) };
    UNITTEST_ASSERT(a2 != b2);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(identical_bool_int)
