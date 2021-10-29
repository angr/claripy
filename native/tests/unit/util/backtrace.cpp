/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <sstream>


/** A non-static function which generates a backtrace */
[[noreturn]] void generate_bt() {
    throw Util::Err::Claricpp { "Test" };
}

/** A static wrapper that has no symbol in the global symbol table */
[[noreturn, gnu::noinline]] static void wrapper3() {
    generate_bt();
}

namespace {
    /** A wrapper in an anonymous namespace */
    [[noreturn, gnu::noinline]] void wrapper2() { wrapper3(); }
} // namespace

/** A non-static wrapper function */
[[noreturn, gnu::noinline]] void wrapper1() {
    wrapper2();
}

/** Test error backtraces */
void backtrace() {
    namespace B = Util::Log::Backend;
    auto old { B::get() };

    // Set logging to be done to a string stream
    auto s { std::make_shared<std::ostringstream>() };
    B::set<B::OStream>(s, true);

    // Generate a backtrace
    const auto backtrace { []() {
        try {
            wrapper1();
        }
        catch (Util::Err::Claricpp &e) {
            return e.backtrace();
        }
        UNITTEST_ERR("Error failed to be caught");
    }() };

    /* In DEBUG mode the backtrace should be something like this:
            4  : 0x40f6c6           : generate_bt() + 38
            5  : /path/to/claripy/native/build/tests/unit/util/util-backtrace.test() [0x40f949]
            6  : /path/to/claripy/native/build/tests/unit/util/util-backtrace.test() [0x40f829]
            7  : 0x40f76a           : backtrace() + 58
            8  : 0x7f0b106ecb7a     : UnitTest::TestLib::test_func(void (&)()) + 26
            9  : 0x40f85b           : main + 43
            10 : 0x7f0b0f11f0b3     : __libc_start_main + 243
            11 : 0x40f5de           : _start + 46
    */

    // Log the backtrace
    B::unsafe_set(std::move(old));
    Util::Log::verbose("Logging caught backtrace");
    Util::Log::verbose(__LINE__, " ", backtrace);

    Util::Log::verbose("Checking backtrace...");
    const auto contains = [&backtrace](CCSC x) { return backtrace.find(x) != std::string::npos; };
    // Ensure the backtrace is valid
    UNITTEST_ASSERT(contains("generate_bt() + "));
    // Note: we do not check the wrappers because of static / anon namespaces
    UNITTEST_ASSERT(contains("backtrace() + "));
    UNITTEST_ASSERT(contains("UnitTest::TestLib::test_func(void"));
    UNITTEST_ASSERT(contains("main + "));
    UNITTEST_ASSERT(contains("start + "));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(backtrace)
