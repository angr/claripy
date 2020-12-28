/** @file */

#include "test_each_level.hpp"
#include "testlib.hpp"
#include "utils.hpp"

#include <iostream>
#include <sstream>


using namespace Utils::Log;
using Lvl = Level::Level;
using namespace UnitTest::TestLib;


#define STR "logged data"
const std::string cst("Custom");


/** Test the given logging function */
void test(std::ostringstream &s, const Lvl l) {
    const auto str = s.str();
    if (UTILS_LOG_LEVEL_IMPLIES(Level::get(), l)) {
        UNITTEST_ASSERT(str.find(STR) != std::string::npos)
    }
    else {
        UNITTEST_ASSERT_MSG(str.size() == 0, WHOAMI)
    }
    s.str(""); // clear the log for the next test
}

/** A custom log type */
UTILS_LOG_DEFINE_LOG_CLASS(Custom)


/** Log levels lower than the set level should be no-op's */
int lower_level_ignored() {

    // Determine if this test case is possible
#ifdef CONSTANT_LOG_LEVEL
    constexpr auto lvl = Level::get();
    if constexpr (lvl == Lvl::Verbose) {
        Utils::Log::warning(
            "Log level is constant and at level Verbose. Unable to test lower levels");
        return 0;
    }
#endif

    // Configure backend and style to output to with all relevant info
    std::ostringstream s;
    Backend::set<Backend::OStream>(s);
    s.str("");
    UNITTEST_ASSERT_MSG(s.str().size() == 0, "Sanity check")

    // Change the log level if needed
#ifndef CONSTANT_LOG_LEVEL
    auto lvl = Level::get();
    if (lvl == Lvl::Verbose) {
        Level::set(Lvl::Warning);
    }
#endif

    // Run tests
    UnitTest::test_each_level(s, test, STR);
    return 0;
}
