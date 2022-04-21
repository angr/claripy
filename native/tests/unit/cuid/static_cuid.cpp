/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A struct that should have a static cuid */
struct HasSCUID1 {
    CUID_DEFINE_MAYBE_UNUSED(0);
};

/** A struct that should have a different static cuid */
struct HasSCUID2 {
    CUID_DEFINE_MAYBE_UNUSED(0);
};

/** A struct whose templates should have different static cuids */
template <int N> struct HasSCUID3 { CUID_DEFINE_MAYBE_UNUSED(N); };

/** A struct whose templates should have identical static cuids */
template <int N> struct HasSCUID4 { CUID_DEFINE_MAYBE_UNUSED(0); };


/** Verify that cuids are unique */
void static_cuid() {
    UNITTEST_ASSERT(HasSCUID1::static_cuid != HasSCUID2::static_cuid);
    UNITTEST_ASSERT(HasSCUID3<0>::static_cuid != HasSCUID3<1>::static_cuid);
    UNITTEST_ASSERT(HasSCUID4<0>::static_cuid == HasSCUID4<1>::static_cuid);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(static_cuid)
