/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** A class with a cuid */
struct A : public CUID {
    /** Use parent constructor */
    using CUID::CUID;
};


/** Verify that the simple_test function works */
void cuid() {}
constexpr Constants::UInt c = 4635;
A a(c);
UNITEST_ASSERT(a.cuid == c);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(cuid)
