/**
 * @file
 * \ingroup unittest
 */
#include <limits>
#include <testlib/testlib.hpp>


/** Returns true if to_hex worked for the chosen value */
template <typename T> static bool test(const T val) {
    std::ostringstream os;
    os << std::hex << "0x" << val;
    const auto sol { os.str() };
    const auto ml { Util::to_hex_max_len<T> };
    UNITTEST_ASSERT(sol.size() <= ml);
    const auto got { Util::to_hex(val) };
    UNITTEST_ASSERT(got.size() <= ml);
    return got == sol;
}

/** Verify to_hex works */
void to_hex() {

    // Test for a few values around boundires and extras
    for (int i { -300 }; i < 300; ++i) {
        UNITTEST_ASSERT_MSG(test(i), "Value: ", i);
    }

    // Test for a few values around boundires and extras
    for (unsigned i { static_cast<unsigned>(-300) }; i < 300; ++i) {
        UNITTEST_ASSERT_MSG(test(i), "Value: ", i);
    }

    // Test for a few values around boundires and extras
    const auto max { std::numeric_limits<int>::max() };
    const auto min { std::numeric_limits<int>::min() };
    for (int i { max - 10 }; i != min + 10; ++i) {
        UNITTEST_ASSERT_MSG(test(i), "Value: ", i);
    }
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(to_hex)