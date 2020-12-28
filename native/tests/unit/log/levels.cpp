/** @file */

#include "test_each_level.hpp"
#include "testlib.hpp"
#include "utils.hpp"

#include <iostream>
#include <sstream>


using namespace Utils::Log;
using Lvl = Level::Level;
using namespace UnitTest::TestLib;


/** The message each log call uses */
#define STR "log test"

/** Test the given logging function */
void test(std::ostringstream &s, Lvl) {
    UNITTEST_ASSERT(s.str().find(STR) != std::string::npos)
    s.str(""); // clear the log for the next test
}


/** Each construction should have a unique pointer */
int levels() {
    // Configure backend and style to output to with all relevant info
    std::ostringstream s;
    Style::set<Style::LevelTimestampMessage>();
    Backend::set<Backend::OStream>(s);

    // Test each level
    UnitTest::test_each_level(s, test, STR);
    return 0;
}
