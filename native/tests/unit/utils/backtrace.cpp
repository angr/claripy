/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"
#include "utils.hpp"

#include <sstream>


/** A non-static function which generates a backtrace */
void generate_bt() {
    using Err = Utils::Error::Claricpp;
    try {
        throw Err("Test");
    }
    catch (Err &) {
    }
}

namespace {
    /** A wrapper in an anonomous namespace */
    void wrapper2() { generate_bt(); }
} // namespace

/** A static wrapper that has no symbol in the global symbol table */
static void wrapper1() {
    wrapper2();
}

/** Test error backtraces */
void backtrace() {
    namespace B = Utils::Log::Backend;

    // Set logging to be done to a string stream
    auto s { std::make_shared<std::ostringstream>() };
    B::set<B::OStream>(s, true);

    // Generate a backtrace
    wrapper1();

    const auto str { s->str() };
    const auto contains = [](const std::string &s, Constants::CCSC x) {
        return s.find(x) != std::string::npos;
    };

    /* The backtrace should be something like this:
            3  : 0x40f6c6           : generate_bt() + 38
            4  : /path/to/claripy/native/build/tests/unit/utils/utils-backtrace.test() [0x40f949]
            5  : /path/to/claripy/native/build/tests/unit/utils/utils-backtrace.test() [0x40f829]
            6  : 0xhome/zwimer40f76a           : backtrace() + 58
            7  : 0x7f0b106ecb7a     : UnitTest::TestLib::test_func(void (&)()) + 26
            8  : 0x40f85b           : main + 43
            9  : 0x7f0b0f11f0b3     : __libc_start_main + 243
            10 : 0x40f5de           : _start + 46
    */

    // Ensure the backtrace is valid
    UNITTEST_ASSERT(contains(str, "generate_bt() + "));
    // Note: we do not check the wrappers because of static / anon namespaces
    UNITTEST_ASSERT(contains(str, "backtrace() + "));
    UNITTEST_ASSERT(contains(str, "UnitTest::TestLib::test_func(void"));
    UNITTEST_ASSERT(contains(str, "main + "));
    UNITTEST_ASSERT(contains(str, "__libc_start_main + "));
    UNITTEST_ASSERT(contains(str, "_start + "));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(backtrace)
