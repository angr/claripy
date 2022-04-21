/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Verify the is_same members work */
void same() {

    // Wrap
    const constexpr bool true3 {
        Util::Type::Is::wrap_same<int, const volatile int, std::remove_cv_t>
    };
    UNITTEST_ASSERT(true3);
    const constexpr bool true4 {
        Util::Type::Is::wrap_same<volatile int, const int, std::remove_cv_t>
    };
    UNITTEST_ASSERT(true4);
    const constexpr bool false3 {
        Util::Type::Is::wrap_same<int, const int, std::remove_volatile_t>
    };
    UNITTEST_ASSERT(not false3);

    // Const
    const constexpr bool true5 { Util::Type::Is::same_ignore_const<const int, int> };
    UNITTEST_ASSERT(true5);
    const constexpr bool true6 { Util::Type::Is::same_ignore_const<int, const int> };
    UNITTEST_ASSERT(true6);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(same)
