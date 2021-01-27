/**
 * @file
 * \ingroup unittest
 */
#include "test_each_level.hpp"
#include "testlib.hpp"
#include "utils.hpp"

#include <iostream>
#include <memory>
#include <ostream>
#include <sstream>


using namespace Utils::Log;
using Lvl = Level::Level;
using namespace UnitTest::TestLib;


/** The message each log call uses */
#define STR "log test"

/** Test the given logging function */
void test(std::shared_ptr<std::ostringstream> &s, Lvl) {
    UNITTEST_ASSERT(s->str().find(STR) != std::string::npos)
    s->str(""); // clear the log for the next test
}


/** Each construction should have a unique pointer */
void levels() {
    // Configure backend and style to output to with all relevant info
    auto s = std::make_shared<std::ostringstream>();
    Style::set<Style::LevelTimestampMessage>();
    Backend::set<Backend::OStream>(std::static_pointer_cast<std::ostream>(s), true);

    // Test each level
    UnitTest::test_each_level(s, test, STR);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(levels)
