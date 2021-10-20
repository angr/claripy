/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Verify the file line hash macros work */
void fnv1a() {

    // The message
    const constexpr CCSC msg { "The quick brown fox jumps over the lazy dog" };
    const constexpr UInt len { Util::strlen(msg) };

    // Verify here: https://asecuritysite.com/encryption/murmur
    static_assert(sizeof(UInt) == sizeof(uint64_t),
                  "fnv1a test case correct message needs to be updated to new size of UInt");
    UInt correct { 0xF3F9B7F5E7E47110 };

    // Hash
    const constexpr auto hash { Util::FNV1a<char>::hash(msg, len) };
    UNITTEST_ASSERT(correct == hash);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(fnv1a)
