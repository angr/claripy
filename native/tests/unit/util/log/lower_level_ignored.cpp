/**
 * @file
 * \ingroup unittest
 */
#include "test_each_level.hpp"
#include "testlib.hpp"

#include <iostream>
#include <sstream>


namespace L = Util::Log;
using Lvl = L::Level::Lvl;
using namespace UnitTest::TestLib;


/** Test the given logging function */
void test(std::shared_ptr<std::ostringstream> &s, const Lvl l) {
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


/** Log levels lower than the set level should be no-op's */
void lower_level_ignored() {
    // Determine if this test case is possible
#ifdef CONSTANT_LOG_LEVEL
    if constexpr (constexpr auto lvl { Level::get() }; lvl == Lvl::Verbose) {
        Util::Log::warning(
            "Log level is constant and at level Verbose. Unable to test lower levels");
        return;
    }
#endif

    // Configure backend and style to output to with all relevant info
    auto s { std::make_shared<std::ostringstream>() };
    s->str("");
    UNITTEST_ASSERT_MSG(s->str().empty(), "Sanity check");
    L::Backend::set<L::Backend::OStream>(Util::Cast::Static::up<std::ostream>(s), true, false);

    // Change the log level if needed
#ifndef CONSTANT_LOG_LEVEL
    if (const auto lvl { L::Level::get() }; lvl == Level::verbose) {
        L::Level::set(Level::warning);
    }
#endif

    // Run tests
    UnitTest::test_each_level(s, test, "Logged data");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(lower_level_ignored)
