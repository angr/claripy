/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"
#include "utils.hpp"


// Invoking this function with the default template argument should compile
template <typename T = bool> void check() {
    if constexpr (std::is_same_v<T, int *>) {
        // This should not fail compilation because of TD::false_
        static_assert(Utils::TD::false_<T>);
    }
}

/** Verify the file line hash macros work */
void td_false() {
    check();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(td_false)
