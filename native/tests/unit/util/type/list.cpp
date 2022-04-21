/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Verify List works
 *  Test is a compilation test
 */
void list() {

    using L1 = Util::Type::List<int, bool>;

    // Append
    using App = Util::Type::List<int, bool, char>;
    static_assert(std::is_same_v<L1::template Append<char>, App>, "List::Append is bad");

    // Prepend
    using Pre = Util::Type::List<char, int, bool>;
    static_assert(std::is_same_v<L1::template Prepend<char>, Pre>, "List::Prepend is bad");

    // Len + Get
    static_assert(L1::len == 2, "List::len is bad");
    static_assert(std::is_same_v<L1::template Get<0>, int>, "List::Get is bad");
    static_assert(std::is_same_v<L1::template Get<1>, bool>, "List::Get is bad");

    // PopFront
    using PF = Util::Type::List<bool>;
    static_assert(std::is_same_v<L1::PopFront, PF>, "List::PopFront is bad");

    // Apply
    using Var = std::variant<int, bool>;
    static_assert(std::is_same_v<L1::Apply<std::variant>, Var>, "List::Apply is bad");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(list)
