/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <utility>


/** Verify the given functions and arguments return a NotSupported exception */
template <typename Fn, typename... Args> static bool is_not_supported(const Fn f, Args &&...args) {
    try {
        f(std::forward<Args>(args)...);
    }
    catch (Utils::Error::Unexpected::NotSupported &) {
        return true;
    }
    return false;
}

/** Test stack limit functions */
void stack_limit() {
    if constexpr (Utils::StackLimit::supported) {
        (void) Utils::StackLimit::get();
        Utils::StackLimit::set(Utils::StackLimit::max());
    }
    else {
        const bool ns_get { is_not_supported(Utils::StackLimit::get) };
        UNITTEST_ASSERT(ns_get);
        const bool ns_max { is_not_supported(Utils::StackLimit::max) };
        UNITTEST_ASSERT(ns_max);
        const bool ns_set { is_not_supported(Utils::StackLimit::set, 0ull) };
        UNITTEST_ASSERT(ns_set);
    }
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(stack_limit)
