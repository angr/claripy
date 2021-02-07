/**
 * @file
 * \ingroup unittest
 */
#include "cuid.hpp"

#include "testlib.hpp"


/** A class with a cuid */
struct A : public CUID::HasCUID {
    /** Constructor */
    A(CUID::CUID c) : HasCUID { c } {}
};


/** Verify that the cuid class works */
void cuid() {
    const constexpr CUID::CUID c { 4635 };
    A a(c);
    UNITTEST_ASSERT(a.cuid == c);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(cuid)
