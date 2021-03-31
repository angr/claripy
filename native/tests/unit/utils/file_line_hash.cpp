/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


// Whitespace padding
// The file line hash *must* be on lines 10 and 11 for test purposes
static const constexpr Constants::UInt my_FLH_10 { UTILS_FILE_LINE_HASH };
static const constexpr Constants::UInt my_FLH_11 { UTILS_FILE_LINE_HASH };
static const constexpr Constants::UInt my_FH { UTILS_FILE_HASH };

// Acquire from linking
extern const Constants::UInt helper_FLH_10;
extern const Constants::UInt helper_FLH_11;
extern const Constants::UInt helper_FH;


/** Verify the file line hash macros work */
void file_line_hash() {

    // Unique file hashes
    UNITTEST_ASSERT(my_FH != helper_FH);

    // Line offset tests
    UNITTEST_ASSERT(my_FLH_10 == my_FH + 10);
    UNITTEST_ASSERT(my_FLH_11 == my_FH + 11);
    UNITTEST_ASSERT(helper_FLH_10 == helper_FH + 10);
    UNITTEST_ASSERT(helper_FLH_11 == helper_FH + 11);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(file_line_hash)
