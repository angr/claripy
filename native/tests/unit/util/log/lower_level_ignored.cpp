/**
 * @file
 * \ingroup unittest
 */
#include "test_each_level.hpp"

#include <iostream>
#include <sstream>
#include <testlib/testlib.hpp>


namespace L = Util::Log;
namespace Lvl = L::Level;
using namespace UnitTest::TestLib;


/** Test the given logging function */
void test(std::shared_ptr<std::ostringstream> &s, const Lvl::Lvl l) {
    const auto str { s->str() };
    if (Level::enabled(l)) {
        UNITTEST_ASSERT(str.find("Logged data") != std::string::npos);
    }
    else {
        UNITTEST_ASSERT_MSG(str.empty(), WHOAMI_HEADER_ONLY);
    }
    s->str(""); // clear the log for the next test
}

/** A custom log type */
UTIL_LOG_DEFINE_LOG_CLASS(Custom)

/** A hack to allow unreachable code not to cause a compile error */
[[maybe_unused]] static UTIL_ICCBOOL allow_unreachable { true };

/** Log levels lower than the set level should be no-op's */
void lower_level_ignored() {
#ifdef CONSTANT_LOG_LEVEL
    // Determine if this test case is possible
    // Note: allow unreachable prevents compiler warnings since this is all cosntexpr else
    if (const auto lvl { Level::get() }; lvl == Lvl::verbose && allow_unreachable) {
        Util::Log::warning(
            "Log level is constant and at level verbose. Unable to test lower levels");
        return;
    }
#endif

    // Configure backend and style to output to with all relevant info
    auto s { std::make_shared<std::ostringstream>() };
    s->str("");
    UNITTEST_ASSERT_MSG(s->str().empty(), "Sanity check");
    L::Backend::set<L::Backend::OStream>(Util::PCast::Static::up<std::ostream>(s), true, false);

    // Change the log level if needed
#ifndef CONSTANT_LOG_LEVEL
    if (const auto lvl { Lvl::get() }; lvl == Level::verbose) {
        Lvl::set(Level::warning);
    }
#endif

    // Run tests
    UnitTest::test_each_level(s, test, "Logged data");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(lower_level_ignored)
