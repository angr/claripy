/**
 * @file
 * @brief A second distinct file from file_line_hash to test the hash
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


// The file line hash *must* be on line 10 for test purposes
extern const U64 helper_FLH_10 { UTIL_FILE_LINE_HASH };
extern const U64 helper_FLH_11 { UTIL_FILE_LINE_HASH };
extern const U64 helper_FH { UTIL_FILE_HASH };
