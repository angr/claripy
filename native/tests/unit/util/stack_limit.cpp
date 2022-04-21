/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>
#include <utility>


/** Verify the given functions and arguments return a NotSupported exception */
template <typename Fn, typename... Args> static bool is_not_supported(const Fn f, Args &&...args) {
    try {
        f(std::forward<Args>(args)...);
    }
    catch (Util::Err::NotSupported &) {
        return true;
    }
    return false;
}

/** Test stack limit functions */
void stack_limit() {
    if constexpr (Util::StackLimit::supported) {
        (void) Util::StackLimit::get();
        Util::StackLimit::set(Util::StackLimit::max());
    }
    else {
        const bool ns_get { is_not_supported(Util::StackLimit::get) };
        UNITTEST_ASSERT(ns_get);
        const bool ns_max { is_not_supported(Util::StackLimit::max) };
        UNITTEST_ASSERT(ns_max);
        const bool ns_set { is_not_supported(Util::StackLimit::set, 0ULL) };
        UNITTEST_ASSERT(ns_set);
    }
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(stack_limit)
