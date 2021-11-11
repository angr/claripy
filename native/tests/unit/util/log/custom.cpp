/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <iostream>
#include <sstream>

/** A custom log type */
UTIL_LOG_DEFINE_LOG_CLASS(Custom)

/** Define test_each_level with the custom log type */
#define TEMPLATE_MACRO <Custom>
#include "test_each_level.hpp"


namespace L = Util::Log;
using Lvl = L::Level::Level;
using namespace UnitTest::TestLib;


/** Test the given logging function */
void test(std::shared_ptr<std::ostringstream> &s, Lvl) {
    auto str { s->str() };
    str.pop_back(); // newline
    UNITTEST_ASSERT(str == "Custom");
    s->str(""); // clear the log for the next test
}

/** Create a style class */
struct CustomSty final : L::Style::Base {
    /** The style function */
    std::string str(CCSC, const Lvl &, const std::ostringstream &) const final { return "Custom"; }
};

/** Each construction should have a unique pointer */
void custom() {
    // Configure backend and style to output to with all relevant info
    auto s { std::make_shared<std::ostringstream>() };
    Style::set<CustomSty>();
    L::Backend::set<L::Backend::OStream>(Util::Cast::Static::up<std::ostream>(s), true);

    // Test each level
    UnitTest::test_each_level(s, test, "");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(custom)
