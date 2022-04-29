/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A struct that should have a static cuid */
struct HasSCUID1 {
    CUID_DEFINE_MAYBE_UNUSED;
};

/** A struct that should have a different static cuid */
struct HasSCUID2 {
    CUID_DEFINE_MAYBE_UNUSED;
};


/** Verify that cuids are unique */
void static_cuid() {
    UNITTEST_ASSERT(HasSCUID1::static_cuid != HasSCUID2::static_cuid);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(static_cuid)
