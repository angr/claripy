/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Verify the file line hash macros work */
void fnv1a() {

    // The message
    const constexpr Constants::CCSC msg { "The quick brown fox jumps over the lazy dog" };
    const constexpr Constants::UInt len { Utils::strlen(msg) };

    // Verify here: https://asecuritysite.com/encryption/murmur
    static_assert(
        sizeof(Constants::UInt) == sizeof(uint64_t),
        "fnv1a test case correct message needs to be updated to new size of Constants::UInt");
    Constants::UInt correct { 0xF3F9B7F5E7E47110 };

    // Hash
    const constexpr auto hash { Utils::FNV1a<char>::hash(msg, len) };
    UNITTEST_ASSERT(correct == hash);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(fnv1a)
