/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <sstream>


/** A non-static function which generates a backtrace */
void generate_bt() {
    using Err = Util::Err::Claricpp;
    try {
        throw Err("Test");
    }
    catch (Err &) {
    }
}

namespace {
    /** A wrapper in an anonymous namespace */
    void wrapper2() { generate_bt(); }
} // namespace

/** A static wrapper that has no symbol in the global symbol table */
static void wrapper1() {
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
    wrapper1();
    const auto backtrace { s->str() };

    /* In DEBUG mode the backtrace should be something like this:
            3  : 0x40f6c6           : generate_bt() + 38
            4  : /path/to/claripy/native/build/tests/unit/util/util-backtrace.test() [0x40f949]
            5  : /path/to/claripy/native/build/tests/unit/util/util-backtrace.test() [0x40f829]
            6  : 0x40f76a           : backtrace() + 58
            7  : 0x7f0b106ecb7a     : UnitTest::TestLib::test_func(void (&)()) + 26
            8  : 0x40f85b           : main + 43
            9  : 0x7f0b0f11f0b3     : __libc_start_main + 243
            10 : 0x40f5de           : _start + 46
    */

    // Log the backtrace
    B::unsafe_set(std::move(old));
    Util::Log::debug(backtrace);

#ifdef DEBUG
    const auto contains = [&backtrace](CCSC x) { return backtrace.find(x) != std::string::npos; };
    // Ensure the backtrace is valid
    UNITTEST_ASSERT(contains("generate_bt() + "));
    // Note: we do not check the wrappers because of static / anon namespaces
    UNITTEST_ASSERT(contains("backtrace() + "));
    UNITTEST_ASSERT(contains("UnitTest::TestLib::test_func(void"));
    UNITTEST_ASSERT(contains("main + "));
    UNITTEST_ASSERT(contains("start + "));
#else
    UNITTEST_ASSERT(backtrace.empty());
#endif
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(backtrace)
