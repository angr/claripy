/**
 * @file
 * \ingroup unittest
 */
#include "test_each_level.hpp"

#include <iostream>
#include <memory>
#include <ostream>
#include <sstream>
#include <testlib/testlib.hpp>


using Lvl = Level::Lvl;
namespace L = Util::Log;
using namespace UnitTest::TestLib;


/** Test the given logging function */
void test(std::shared_ptr<std::ostringstream> &s, Lvl) {
    UNITTEST_ASSERT(s->str().find("Log test") != std::string::npos);
    s->str(""); // clear the log for the next test
}

/** Each construction should have a unique pointer */
void levels() {
    // Configure backend and style to output to with all relevant info
    L::Style::set<L::Style::LevelTimestampMessage>();
    auto s { std::make_shared<std::ostringstream>() };
    L::Backend::set<L::Backend::OStream>(Util::PCast::Static::up<std::ostream>(s), true);

    // Test each level
    UnitTest::test_each_level(s, test, "Log test");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(levels)
