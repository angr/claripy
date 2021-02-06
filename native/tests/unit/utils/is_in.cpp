/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** A base struct */
struct A {};

/** A derived struct */
struct B : public A {};


/** Verify the is_in members work */
void is_in() {

    // Trivial
    const constexpr bool empty { Utils::qualified_is_in<int> };
    UNITTEST_ASSERT(!empty);

    // Basic
    const constexpr bool true1 { Utils::qualified_is_in<int, unsigned, bool, int> };
    UNITTEST_ASSERT(true1);
    const constexpr bool false1 { Utils::qualified_is_in<int, unsigned, bool, char> };
    UNITTEST_ASSERT(!false1);
    // Fail because of const
    const constexpr bool false2 { Utils::qualified_is_in<const int, unsigned, bool, int> };
    UNITTEST_ASSERT(!false2);
    const constexpr bool false3 { Utils::qualified_is_in<int, unsigned, bool, const int> };
    UNITTEST_ASSERT(!false3);
    // Ancestor failure
    const constexpr bool false4 { Utils::qualified_is_in<B, unsigned, bool, A> };
    UNITTEST_ASSERT(!false4);


    // Transfer const
    const constexpr bool true2 { Utils::ignore_const_is_in<int, unsigned, bool, const int> };
    UNITTEST_ASSERT(true2);
    const constexpr bool true3 { Utils::ignore_const_is_in<const int, unsigned, bool, const int> };
    UNITTEST_ASSERT(true3);
    // Ancestor failure
    const constexpr bool false5 { Utils::ignore_const_is_in<B, unsigned, bool, A> };
    UNITTEST_ASSERT(!false5);

    // Ancestor
    const constexpr bool true4 { Utils::ancestor_is_in<B, unsigned, bool, A> };
    UNITTEST_ASSERT(true4);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(is_in)
