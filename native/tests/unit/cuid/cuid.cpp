/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A class with a cuid */
struct TestCUID : public CUID::HasCUID {
    /** Constructor */
    TestCUID(CUID::CUID c) : HasCUID { c } {}
};


/** Verify that the cuid class works */
void cuid() {
    const constexpr CUID::CUID c { 4635 };
    TestCUID a { c };
    UNITTEST_ASSERT(a.cuid == c);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(cuid)
