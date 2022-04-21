/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** A base struct */
struct TestBase {};

/** A derived struct */
struct TestDerived : public TestBase {};


/** Verify the is_in members work */
void in() {

    // Trivial
    const constexpr bool empty { Util::Type::Is::in<int> };
    UNITTEST_ASSERT(!empty);

    // Basic
    const constexpr bool true1 { Util::Type::Is::in<int, unsigned, bool, int> };
    UNITTEST_ASSERT(true1);
    const constexpr bool false1 { Util::Type::Is::in<int, unsigned, bool, char> };
    UNITTEST_ASSERT(!false1);
    // Fail because of const
    const constexpr bool false2 { Util::Type::Is::in<const int, unsigned, bool, int> };
    UNITTEST_ASSERT(!false2);
    const constexpr bool false3 { Util::Type::Is::in<int, unsigned, bool, const int> };
    UNITTEST_ASSERT(!false3);
    // Ancestor failure
    const constexpr bool false4 { Util::Type::Is::in<TestDerived, unsigned, bool, TestBase> };
    UNITTEST_ASSERT(!false4);


    // Transfer const
    const constexpr bool true2 { Util::Type::Is::in_ignore_const<int, unsigned, bool, const int> };
    UNITTEST_ASSERT(true2);
    const constexpr bool true3 {
        Util::Type::Is::in_ignore_const<const int, unsigned, bool, const int>
    };
    UNITTEST_ASSERT(true3);
    // Ancestor failure
    const constexpr bool false5 {
        Util::Type::Is::in_ignore_const<TestDerived, unsigned, bool, TestBase>
    };
    UNITTEST_ASSERT(!false5);

    // Ancestor
    const constexpr bool true4 {
        Util::Type::Is::ancestor_in<TestDerived, unsigned, bool, TestBase>
    };
    UNITTEST_ASSERT(true4);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(in)
