/**
 * @file
 * \ingroup unittest
 */
#include <sstream>
#include <testlib/testlib.hpp>


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
    [[noreturn, gnu::noinline]] void wrapper2() {
        wrapper3();
    }
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
    B::silent_set<B::OStream>(s, true);

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

    /* In DEBUG mode the backtrace **might** be something like this.
     * We support multiple back trace options; some with source snippets some with file names
     * etc; regardless, the tests below should pass for *every* backtrace format we support
     * Linux:
        3  : 0x558d4698d795     : generate_bt() + 39
        4  : /path/to/build/tests/unit/util/util-backtrace.test(+0x157d2) [0x558d4698d7d2]
        5  : 0x558d4698d7df     : wrapper1() + 0
        6  : /path/to/build/tests/unit/util/util-backtrace.test(+0x157ec) [0x558d4698d7ec]
        7  : /path/to/build/tests/unit/util/util-backtrace.test(+0x15810) [0x558d4698d810]
        8  : 0x558d4698d8f4     : backtrace() + 94
        9  : 0x7f6012a86386     : UnitTest::TestLib::test_func(void (&)()) + 45
        10 : 0x558d4698dbeb     : main + 139
        11 : 0x7f60113490b3     : __libc_start_main + 243
        12 : 0x558d4698d5ee     : _start + 46
     * MacOS:
        4  : 0x10bc35d08        : generate_bt() + 40
        5  : 0x10bc385f9        : wrapper3() + 9
        6  : 0x10bc35db9        : (anonymous namespace)::wrapper2() + 9
        7  : 0x10bc35da9        : wrapper1() + 9
        8  : 0x10bc362b0        : backtrace()::$_0::operator()() const + 32
        9  : 0x10bc35e05        : backtrace() + 69
        10 : 0x10bd0cb78        : UnitTest::TestLib::test_func(void (&)()) + 24
        11 : 0x10bc36676        : main + 102
        12 : 0x7fff20503f3d     : start + 1
        13 : 0x1                : 0x0 + 1
     */

    // Log the backtrace
    B::silent_less_safe_set(std::move(old));
    Util::Log::info("Logging caught backtrace");
    Util::Log::debug(WHOAMI, backtrace);

    Util::Log::info("Checking backtrace...");
    const auto contains = [&backtrace](CCSC x) { return backtrace.find(x) != std::string::npos; };
    // Ensure the backtrace is valid
#if defined(DEBUG) || defined(__linux__)
    UNITTEST_ASSERT(contains("generate_bt()"));
    // Note: we do not check the other wrappers because of lambdas / static / anon namespaces
    UNITTEST_ASSERT(contains("wrapper1()"));
    UNITTEST_ASSERT(contains("backtrace()"));
    UNITTEST_ASSERT(contains("UnitTest::TestLib::test_func(void"));
    UNITTEST_ASSERT(contains("main"));
#else
    UNITTEST_ASSERT(contains("util-backtrace.test"));
    UNITTEST_ASSERT(contains("UnitTest::TestLib::test_func(void"));
#endif
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(backtrace)
