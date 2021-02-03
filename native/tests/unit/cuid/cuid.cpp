/**
 * @file
 * \ingroup unittest
 */
#include "cuid.hpp"

#include "testlib.hpp"


/** A class with a cuid */
struct A : public CUID {
    /** Constructor */
    A(Constants::UInt c) : CUID { c } {}
};


/** Verify that the simple_test function works */
void cuid() {
    constexpr Constants::UInt c = 4635;
    A a(c);
    UNITTEST_ASSERT(a.cuid == c);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(cuid)
