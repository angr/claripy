/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Verify the is_same members work */
void is_same() {

    // Exact
    const constexpr bool true1 { Util::is_exactly_same<int, int> };
    UNITTEST_ASSERT(true1);
    const constexpr bool false1 { Util::is_exactly_same<const int, int> };
    UNITTEST_ASSERT(!false1);
    const constexpr bool false2 { Util::is_exactly_same<int, const int> };
    UNITTEST_ASSERT(!false2);
    const constexpr bool true2 { Util::is_exactly_same<const int, const int> };
    UNITTEST_ASSERT(true2);

    // Wrap
    const constexpr bool true3 { Util::is_wrap_same<int, const volatile int, std::remove_cv_t> };
    UNITTEST_ASSERT(true3);
    const constexpr bool true4 { Util::is_wrap_same<volatile int, const int, std::remove_cv_t> };
    UNITTEST_ASSERT(true4);
    const constexpr bool false3 { Util::is_wrap_same<int, const int, std::remove_volatile_t> };
    UNITTEST_ASSERT(!false3);

    // Const
    const constexpr bool true5 { Util::is_same_ignore_const<const int, int> };
    UNITTEST_ASSERT(true5);
    const constexpr bool true6 { Util::is_same_ignore_const<int, const int> };
    UNITTEST_ASSERT(true6);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(is_same)
