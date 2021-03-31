
/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** A type */
using Internal = const char;
/** A container of Internals */
using Container = std::shared_ptr<Internal>;
/** The extracted type */
using Extracted = Utils::InternalType<Container>;


/** Verify InternalType works */
void internal_type() {
    const bool true_ { std::is_same_v<Internal, Extracted> };
    UNITTEST_ASSERT(true_);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(internal_type)
